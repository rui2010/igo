(() => {
  'use strict';

  // 定数
  const LINE_COLOR = '#333';
  const STAR_COLOR = '#333';
  const BOARD_COLOR = '#d8c089';
  const BLACK = 1; // 黒
  const WHITE = 2; // 白

  // ユーティリティ
  const opposite = (c) => (c === BLACK ? WHITE : BLACK);

  // GameState
  class GameState {
    constructor(size = 19) {
      this.size = size;
      this.board = new Array(size * size).fill(0); // 0:空, 1:黒, 2:白
      this.turn = BLACK;
      this.captures = { [BLACK]: 0, [WHITE]: 0 };
      this.history = []; // 直前状態のスナップショットを積む
      this.passesInRow = 0;
      this.prevBoardHash = null; // 直前局面ハッシュ(単純コウ用)
      this.showCoords = false;
      this.gameOver = false;
    }
    cloneBoard() { return this.board.slice(); }
    idx(x, y) { return y * this.size + x; }
    inside(x, y) { return x >= 0 && x < this.size && y >= 0 && y < this.size; }
    at(x, y) { return this.board[this.idx(x, y)]; }
    set(x, y, v) { this.board[this.idx(x, y)] = v; }
    hash() {
      // Zobristの代わりに簡易ハッシュ(十分ではないがコウ検出には実用)
      let h = 1469598103934665603n;
      const FNV_PRIME = 1099511628211n;
      for (let i = 0; i < this.board.length; i++) {
        h ^= BigInt(this.board[i] + 1);
        h *= FNV_PRIME;
      }
      return h.toString();
    }
    // 履歴用スナップショット
    snapshot() {
      return {
        size: this.size,
        board: this.cloneBoard(),
        turn: this.turn,
        captures: { [BLACK]: this.captures[BLACK], [WHITE]: this.captures[WHITE] },
        passesInRow: this.passesInRow,
        prevBoardHash: this.prevBoardHash,
        showCoords: this.showCoords,
        gameOver: this.gameOver,
      };
    }
    restore(s) {
      this.size = s.size;
      this.board = s.board.slice();
      this.turn = s.turn;
      this.captures = { [BLACK]: s.captures[BLACK], [WHITE]: s.captures[WHITE] };
      this.passesInRow = s.passesInRow;
      this.prevBoardHash = s.prevBoardHash;
      this.showCoords = s.showCoords;
      this.gameOver = s.gameOver;
    }
  }

  // 連結・呼吸点計算
  function floodGroup(gs, sx, sy) {
    const color = gs.at(sx, sy);
    const stack = [[sx, sy]];
    const visited = new Set([gs.idx(sx, sy)]);
    const stones = [];
    const liberties = new Set();
    const dirs = [[1,0],[-1,0],[0,1],[0,-1]];
    while (stack.length) {
      const [x,y] = stack.pop();
      stones.push([x,y]);
      for (const [dx,dy] of dirs) {
        const nx = x + dx, ny = y + dy;
        if (!gs.inside(nx, ny)) continue;
        const v = gs.at(nx, ny);
        if (v === 0) { liberties.add(gs.idx(nx, ny)); continue; }
        if (v === color) {
          const id = gs.idx(nx, ny);
          if (!visited.has(id)) { visited.add(id); stack.push([nx,ny]); }
        }
      }
    }
    return { stones, liberties };
  }

  function placeLegal(gs, x, y) {
    if (!gs.inside(x,y) || gs.at(x,y) !== 0) return { ok:false, reason:'occupied' };
    const me = gs.turn;
    const opp = opposite(me);

    const snapshot = gs.cloneBoard();
    gs.set(x,y, me);

    // 隣接相手連結の呼吸点が0なら取り除く
    const dirs = [[1,0],[-1,0],[0,1],[0,-1]];
    let totalCaptured = 0;
    for (const [dx,dy] of dirs) {
      const nx = x+dx, ny = y+dy;
      if (!gs.inside(nx,ny)) continue;
      if (gs.at(nx,ny) === opp) {
        const { stones, liberties } = floodGroup(gs, nx, ny);
        if (liberties.size === 0) {
          // 取り
          for (const [sx,sy] of stones) gs.set(sx,sy,0);
          totalCaptured += stones.length;
        }
      }
    }

    // 自殺手チェック
    const { liberties: myLib } = floodGroup(gs, x, y);
    if (myLib.size === 0 && totalCaptured === 0) {
      // 戻す
      gs.board = snapshot;
      return { ok:false, reason:'suicide' };
    }

    // 単純コウ: 直前局面と同一局面への戻りを禁止
    const newHash = gs.hash();
    if (newHash === gs.prevBoardHash) {
      gs.board = snapshot;
      return { ok:false, reason:'ko' };
    }

    return { ok:true, captured: totalCaptured, newHash };
  }

  function applyMove(gs, x, y) {
    const pre = gs.snapshot();
    const res = placeLegal(gs, x, y);
    if (!res.ok) return res;
    // 事前状態を履歴に保存
    gs.history.push(pre);
    // アゲハマ加算
    if (res.captured) gs.captures[gs.turn] += res.captured;
    // 次手番
    gs.prevBoardHash = gs.hash();
    gs.turn = opposite(gs.turn);
    gs.passesInRow = 0;
    return { ok:true };
  }

  function passMove(gs) {
    if (gs.gameOver) return;
    // 事前状態を履歴に保存
    gs.history.push(gs.snapshot());
    gs.prevBoardHash = gs.hash();
    gs.turn = opposite(gs.turn);
    gs.passesInRow += 1;
    if (gs.passesInRow >= 2) gs.gameOver = true;
  }

  function undoMove(gs) {
    if (gs.history.length === 0) return false;
    const snap = gs.history.pop();
    gs.restore(snap);
    return true;
  }

  // スコア推定: 囲まれた地の簡易推定(石に接する空点の連結を数え、単色接触ならその色の地)
  function estimateScore(gs, komi = 6.5) {
    const size = gs.size;
    const visited = new Set();
    const dirs = [[1,0],[-1,0],[0,1],[0,-1]];
    let blackTerr = 0, whiteTerr = 0;

    function floodEmpty(sx, sy) {
      const stack = [[sx,sy]];
      const empties = [];
      const touching = new Set();
      visited.add(gs.idx(sx,sy));
      while (stack.length) {
        const [x,y] = stack.pop();
        empties.push([x,y]);
        for (const [dx,dy] of dirs) {
          const nx=x+dx, ny=y+dy;
          if (!gs.inside(nx,ny)) continue;
          const v = gs.at(nx,ny);
          if (v === 0) {
            const id = gs.idx(nx,ny);
            if (!visited.has(id)) { visited.add(id); stack.push([nx,ny]); }
          } else {
            touching.add(v);
          }
        }
      }
      return { empties, touching };
    }

    for (let y=0; y<size; y++) {
      for (let x=0; x<size; x++) {
        if (gs.at(x,y) === 0 && !visited.has(gs.idx(x,y))) {
          const { empties, touching } = floodEmpty(x,y);
          if (touching.size === 1) {
            const color = [...touching][0];
            if (color === BLACK) blackTerr += empties.length; else whiteTerr += empties.length;
          }
        }
      }
    }

    const blackScore = blackTerr + gs.captures[BLACK];
    const whiteScore = whiteTerr + gs.captures[WHITE] + komi;
    return { blackTerr, whiteTerr, blackScore, whiteScore, komi };
  }

  // 描画
  class Renderer {
    constructor(canvas, gs) {
      this.canvas = canvas;
      this.ctx = canvas.getContext('2d');
      this.gs = gs;
      this.padding = 30;
      this.stoneRadius = 16;
      this.resize();
      window.addEventListener('resize', () => this.resize());
    }
    resize() {
      const rect = this.canvas.getBoundingClientRect();
      const size = Math.min(rect.width, rect.height);
      // 固定ピクセルキャンバスだが、CSSで拡大縮小
      this.gridSize = (this.canvas.width - this.padding*2) / (this.gs.size - 1);
      this.stoneRadius = this.gridSize * 0.48;
      this.draw();
    }
    boardToPix(x, y) {
      return [this.padding + x * this.gridSize, this.padding + y * this.gridSize];
    }
    clear() {
      const { ctx, canvas } = this;
      ctx.fillStyle = BOARD_COLOR;
      ctx.fillRect(0,0,canvas.width, canvas.height);
    }
    drawGrid() {
      const { ctx } = this;
      ctx.strokeStyle = LINE_COLOR;
      ctx.lineWidth = 1;
      const n = this.gs.size;
      for (let i=0; i<n; i++) {
        const [x0,y0] = this.boardToPix(0,i);
        const [x1,y1] = this.boardToPix(n-1,i);
        ctx.beginPath(); ctx.moveTo(x0,y0); ctx.lineTo(x1,y1); ctx.stroke();
        const [xx0,yy0] = this.boardToPix(i,0);
        const [xx1,yy1] = this.boardToPix(i,n-1);
        ctx.beginPath(); ctx.moveTo(xx0,yy0); ctx.lineTo(xx1,yy1); ctx.stroke();
      }
      // 星
      const stars = starPoints(n);
      ctx.fillStyle = STAR_COLOR;
      for (const [sx,sy] of stars) {
        const [px,py] = this.boardToPix(sx,sy);
        ctx.beginPath(); ctx.arc(px,py, 3, 0, Math.PI*2); ctx.fill();
      }
      if (this.gs.showCoords) this.drawCoords();
    }
    drawCoords() {
      const { ctx } = this;
      ctx.fillStyle = '#222';
      ctx.font = '12px sans-serif';
      ctx.textAlign = 'center';
      ctx.textBaseline = 'top';
      const letters = coordLetters(this.gs.size);
      for (let x=0; x<this.gs.size; x++) {
        const [px,py] = this.boardToPix(x,0);
        ctx.fillText(letters[x], px, 6);
      }
      ctx.textAlign = 'right';
      ctx.textBaseline = 'middle';
      for (let y=0; y<this.gs.size; y++) {
        const [px,py] = this.boardToPix(0,y);
        ctx.fillText(String(this.gs.size - y), 24, py);
      }
    }
    drawStones() {
      const { ctx } = this;
      for (let y=0; y<this.gs.size; y++) {
        for (let x=0; x<this.gs.size; x++) {
          const v = this.gs.at(x,y);
          if (v === 0) continue;
          const [px,py] = this.boardToPix(x,y);
          drawStone(ctx, px, py, this.stoneRadius, v === BLACK ? 'black' : 'white');
        }
      }
    }
    drawTurnMarker() {
      const { ctx } = this;
      ctx.save();
      const color = this.gs.turn === BLACK ? 'black' : 'white';
      ctx.globalAlpha = 0.35;
      const [px,py] = this.boardToPix(0,0);
      ctx.fillStyle = color;
      ctx.fillRect(8, this.canvas.height-18, 10, 10);
      ctx.restore();
    }
    draw() {
      this.clear();
      this.drawGrid();
      this.drawStones();
      this.drawTurnMarker();
    }
  }

  function drawStone(ctx, x, y, r, color) {
    // 簡易グラデーション
    const grd = ctx.createRadialGradient(x - r*0.3, y - r*0.3, r*0.1, x, y, r);
    if (color === 'black') {
      grd.addColorStop(0, '#666');
      grd.addColorStop(1, '#111');
    } else {
      grd.addColorStop(0, '#fff');
      grd.addColorStop(1, '#dcdcdc');
    }
    ctx.beginPath(); ctx.arc(x,y,r,0,Math.PI*2);
    ctx.fillStyle = grd; ctx.fill();
    ctx.strokeStyle = '#00000022'; ctx.stroke();
  }

  function starPoints(n) {
    if (n < 7) return [];
    const pts = [];
    const pos = n === 9 ? [2,4,6] : n === 13 ? [3,6,9] : [3,9,15];
    for (const y of pos) for (const x of pos) pts.push([x,y]);
    return pts;
  }
  function coordLetters(n) {
    const letters = 'ABCDEFGHJKLMNOPQRSTUVWXYZ';
    return letters.slice(0,n).split('');
  }

  // UI
  const canvas = document.getElementById('board');
  const ui = {
    turn: document.getElementById('turn'),
    captures: document.getElementById('captures'),
    passes: document.getElementById('passes'),
    sizeSel: document.getElementById('boardSize'),
    newGame: document.getElementById('newGame'),
    undo: document.getElementById('undoMove'),
    pass: document.getElementById('passMove'),
    toggleCoords: document.getElementById('toggleCoords'),
    estimate: document.getElementById('estimateScore'),
  };

  let gs = new GameState(parseInt(ui.sizeSel.value,10));
  const renderer = new Renderer(canvas, gs);

  function updateStatus() {
    ui.turn.textContent = `手番: ${gs.turn === BLACK ? '黒' : '白'}`;
    ui.captures.textContent = `黒アゲハマ: ${gs.captures[BLACK]} / 白アゲハマ: ${gs.captures[WHITE]}`;
    ui.passes.textContent = `連続パス: ${gs.passesInRow}`;
  }

  function canvasToBoard(ev) {
    const rect = canvas.getBoundingClientRect();
    const x = ev.clientX - rect.left;
    const y = ev.clientY - rect.top;
    // 最も近い交点へスナップ
    const gx = Math.round((x - renderer.padding) / renderer.gridSize);
    const gy = Math.round((y - renderer.padding) / renderer.gridSize);
    return { x: gx, y: gy };
  }

  canvas.addEventListener('click', (ev) => {
    if (gs.gameOver) return;
    const { x, y } = canvasToBoard(ev);
    const res = applyMove(gs, x, y);
    if (!res.ok) {
      let msg = '着手不可';
      if (res.reason === 'occupied') msg = 'そこには打てません(占有)';
      if (res.reason === 'suicide') msg = '自殺手は禁止です';
      if (res.reason === 'ko') msg = 'コウで禁止されています';
      flash(msg);
      return;
    }
    renderer.draw();
    updateStatus();
  });

  ui.newGame.addEventListener('click', () => {
    gs = new GameState(parseInt(ui.sizeSel.value,10));
    renderer.gs = gs; renderer.resize(); renderer.draw();
    updateStatus();
  });

  ui.undo.addEventListener('click', () => {
    if (undoMove(gs)) { renderer.draw(); updateStatus(); }
    else { flash('これ以上戻せません'); }
  });

  ui.pass.addEventListener('click', () => {
    passMove(gs);
    renderer.draw();
    updateStatus();
    if (gs.gameOver) flash('終局しました。地合い推定を実行できます。');
  });

  ui.toggleCoords.addEventListener('click', () => {
    gs.showCoords = !gs.showCoords; renderer.draw();
  });

  ui.estimate.addEventListener('click', () => {
    const s = estimateScore(gs);
    const winner = s.blackScore === s.whiteScore ? '持碁(引き分け)' : (s.blackScore > s.whiteScore ? '黒番勝ち' : '白番勝ち');
    flash(`推定: 黒 ${s.blackScore.toFixed(1)} 点, 白 ${(s.whiteScore).toFixed(1)} 点 (コミ ${s.komi}) → ${winner}`);
  });

  function flash(message) {
    const div = document.createElement('div');
    div.textContent = message;
    div.style.position = 'fixed';
    div.style.left = '50%';
    div.style.top = '12px';
    div.style.transform = 'translateX(-50%)';
    div.style.background = 'rgba(0,0,0,0.85)';
    div.style.color = '#fff';
    div.style.padding = '8px 12px';
    div.style.borderRadius = '6px';
    div.style.fontSize = '14px';
    div.style.zIndex = 9999;
    document.body.appendChild(div);
    setTimeout(() => { div.remove(); }, 2000);
  }

  // 初期描画
  renderer.draw();
  updateStatus();
})();
