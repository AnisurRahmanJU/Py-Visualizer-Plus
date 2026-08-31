/* =========================================================================
   PyInterpreter — tokenizer, indentation-aware parser, and a step-tracing
   evaluator for a teaching subset of Python.
   ========================================================================= */
class PyInterpreter {
  constructor(code, stdinQ) {
    this.code = code;
    this.steps = [];
    this.errors = [];
    this.stdinQueue = stdinQ || [];
    this._stdinIdx = 0;
    this.output = '';
    this._addrCtr = 0x1000;
    this._heap = {};
    this.functions = {};
    this._globalFrame = { name: '[Global]', vars: {}, isGlobal: true };
    this._callStack = [];
    try {
      this._tokenize();
      this._ti = 0;
      const prog = this._parseProgram();
      this._run(prog);
    } catch (e) {
      this.errors.push(e.message || String(e));
    }
  }

  _heapAddr() { const a = '0x' + this._addrCtr.toString(16).toUpperCase(); this._addrCtr += 8; return a; }

  _tokenize() {
    const lines = this.code.replace(/\r\n/g, '\n').replace(/\t/g, '        ').split('\n');
    this.tokens = [];
    const indentStack = [0];
    let bracketDepth = 0;
    let cont = false;

    for (let ln = 0; ln < lines.length; ln++) {
      let raw = lines[ln];
      let i = 0;

      if (bracketDepth === 0 && !cont) {
        let indent = 0;
        while (i < raw.length && raw[i] === ' ') { indent++; i++; }
        const rest = raw.slice(i);
        if (rest.trim() === '' || rest.trim().startsWith('#')) continue;
        if (indent > indentStack[indentStack.length - 1]) {
          indentStack.push(indent);
          this.tokens.push({ t: 'INDENT', ln: ln + 1 });
        }
        while (indent < indentStack[indentStack.length - 1]) {
          indentStack.pop();
          this.tokens.push({ t: 'DEDENT', ln: ln + 1 });
        }
      }
      cont = false;

      let hadToken = false;
      while (i < raw.length) {
        const c = raw[i];
        if (c === ' ') { i++; continue; }
        if (c === '#') break;
        if (c === '\\' && i === raw.length - 1) { cont = true; i++; continue; }

        if (/[0-9]/.test(c) || (c === '.' && /[0-9]/.test(raw[i + 1] || ''))) {
          let s = i, isF = false;
          while (i < raw.length && (/[0-9]/.test(raw[i]) || (raw[i] === '.' && !isF))) {
            if (raw[i] === '.') isF = true;
            i++;
          }
          if (raw[i] === 'e' || raw[i] === 'E') {
            isF = true; i++;
            if (raw[i] === '+' || raw[i] === '-') i++;
            while (/[0-9]/.test(raw[i] || '')) i++;
          }
          const numStr = raw.slice(s, i);
          this.tokens.push({ t: 'num', v: isF ? parseFloat(numStr) : parseInt(numStr, 10), isFloat: isF, ln: ln + 1 });
          hadToken = true; continue;
        }

        if (/[a-zA-Z_]/.test(c)) {
          let s = i; while (i < raw.length && /[a-zA-Z0-9_]/.test(raw[i])) i++;
          const idv = raw.slice(s, i);
          if ((idv === 'f' || idv === 'r' || idv === 'rb' || idv === 'fr' || idv === 'b') && (raw[i] === '"' || raw[i] === "'")) {
            const isF = idv.includes('f');
            const quote = raw[i]; i++;
            let sres = '';
            while (i < raw.length && raw[i] !== quote) {
              if (raw[i] === '\\') {
                const e = raw[i + 1];
                sres += e === 'n' ? '\n' : e === 't' ? '\t' : e === '\\' ? '\\' : e === quote ? quote : (e || '');
                i += 2;
              } else { sres += raw[i]; i++; }
            }
            i++;
            this.tokens.push({ t: isF ? 'fstr' : 'str', v: sres, ln: ln + 1 });
            hadToken = true; continue;
          }
          this.tokens.push({ t: 'id', v: idv, ln: ln + 1 });
          hadToken = true; continue;
        }

        if (c === '"' || c === "'") {
          const quote = c;
          if (raw[i + 1] === quote && raw[i + 2] === quote) {
            let s = ''; i += 3; const startLn = ln;
            while (true) {
              if (i >= raw.length) {
                s += '\n'; ln++;
                if (ln >= lines.length) break;
                raw = lines[ln]; i = 0; continue;
              }
              if (raw[i] === quote && raw[i + 1] === quote && raw[i + 2] === quote) { i += 3; break; }
              s += raw[i]; i++;
            }
            this.tokens.push({ t: 'str', v: s, ln: startLn + 1 });
            hadToken = true; continue;
          }
          i++; let s = '';
          while (i < raw.length && raw[i] !== quote) {
            if (raw[i] === '\\') {
              const e = raw[i + 1];
              s += e === 'n' ? '\n' : e === 't' ? '\t' : e === '\\' ? '\\' : e === quote ? quote : (e || '');
              i += 2;
            } else { s += raw[i]; i++; }
          }
          i++;
          this.tokens.push({ t: 'str', v: s, ln: ln + 1 });
          hadToken = true; continue;
        }

        const three = raw.slice(i, i + 3);
        if (three === '**=' || three === '//=') { this.tokens.push({ t: 'op', v: three, ln: ln + 1 }); i += 3; hadToken = true; continue; }
        const two = raw.slice(i, i + 2);
        if (['==', '!=', '<=', '>=', '->', '**', '//', '+=', '-=', '*=', '/=', '%=', ':='].includes(two)) {
          this.tokens.push({ t: 'op', v: two, ln: ln + 1 }); i += 2; hadToken = true; continue;
        }
        if ('()[]{}:,.+-*/%<>=!'.includes(c)) {
          if ('([{'.includes(c)) bracketDepth++;
          if (')]}'.includes(c)) bracketDepth = Math.max(0, bracketDepth - 1);
          this.tokens.push({ t: 'op', v: c, ln: ln + 1 }); i++; hadToken = true; continue;
        }
        i++;
      }
      if (hadToken && bracketDepth === 0 && !cont) this.tokens.push({ t: 'NEWLINE', ln: ln + 1 });
    }
    while (indentStack.length > 1) { indentStack.pop(); this.tokens.push({ t: 'DEDENT', ln: lines.length + 1 }); }
    this.tokens.push({ t: 'eof', ln: lines.length + 1 });
  }

  _pk(o = 0) { return this.tokens[this._ti + o] || { t: 'eof', v: '', ln: 0 }; }
  _nx() { return this.tokens[this._ti++] || { t: 'eof', v: '', ln: 0 }; }
  _exOp(v) { const t = this._nx(); if (t.v !== v) throw new Error(`Expected '${v}' but got '${t.v}' near line ${t.ln}`); return t; }
  _isKw(v) { const t = this._pk(); return t.t === 'id' && t.v === v; }
  _skipNL() { while (this._pk().t === 'NEWLINE') this._nx(); }

  _parseProgram() {
    const stmts = [];
    this._skipNL();
    while (this._pk().t !== 'eof') { stmts.push(this._parseStmt()); this._skipNL(); }
    return stmts;
  }

  _parseBlock() {
    if (this._pk().t === 'NEWLINE') {
      this._skipNL();
      if (this._pk().t !== 'INDENT') throw new Error(`Expected indented block near line ${this._pk().ln}`);
      this._nx();
      const stmts = [];
      this._skipNL();
      while (this._pk().t !== 'DEDENT' && this._pk().t !== 'eof') { stmts.push(this._parseStmt()); this._skipNL(); }
      if (this._pk().t === 'DEDENT') this._nx();
      return stmts;
    }
    return [this._parseStmt()];
  }

  _parseStmt() {
    const t = this._pk();
    if (t.t === 'id') {
      switch (t.v) {
        case 'if': return this._parseIf();
        case 'while': return this._parseWhile();
        case 'for': return this._parseFor();
        case 'def': return this._parseDef();
        case 'return': return this._parseReturn();
        case 'break': this._nx(); this._skipNL(); return { type: 'break', ln: t.ln };
        case 'continue': this._nx(); this._skipNL(); return { type: 'continue', ln: t.ln };
        case 'pass': this._nx(); this._skipNL(); return { type: 'pass', ln: t.ln };
        case 'global': case 'nonlocal': case 'import': case 'from':
          while (this._pk().t !== 'NEWLINE' && this._pk().t !== 'eof') this._nx();
          this._skipNL(); return { type: 'pass', ln: t.ln };
      }
    }
    const ln = t.ln;
    const target = this._parseExprList();
    const assignOps = ['=', '+=', '-=', '*=', '/=', '//=', '%=', '**='];
    if (this._pk().t === 'op' && assignOps.includes(this._pk().v)) {
      const op = this._nx().v;
      const value = this._parseExprList();
      this._skipNL();
      return { type: 'assign', op, target, value, ln };
    }
    this._skipNL();
    return { type: 'expr', expr: target, ln };
  }

  _parseExprList() {
    const first = this._parseExpr();
    if (this._pk().t === 'op' && this._pk().v === ',') {
      const items = [first];
      while (this._pk().t === 'op' && this._pk().v === ',') {
        this._nx();
        if (this._pk().t === 'NEWLINE' || this._pk().t === 'eof') break;
        if (this._pk().t === 'op' && ['=', '+=', '-=', '*=', '/=', '//=', '%=', '**='].includes(this._pk().v)) break;
        items.push(this._parseExpr());
      }
      return { type: 'tuple', items, ln: first.ln };
    }
    return first;
  }

  _parseIf() {
    const ln = this._nx().ln;
    const cond = this._parseExpr();
    this._exOp(':');
    const then = this._parseBlock();
    let elseBranch = null;
    this._skipNL();
    if (this._isKw('elif')) elseBranch = [this._parseIf()];
    else if (this._isKw('else')) { this._nx(); this._exOp(':'); elseBranch = this._parseBlock(); }
    return { type: 'if', cond, then, else: elseBranch, ln };
  }

  _parseWhile() {
    const ln = this._nx().ln;
    const cond = this._parseExpr();
    this._exOp(':');
    const body = this._parseBlock();
    let elseBranch = null;
    this._skipNL();
    if (this._isKw('else')) { this._nx(); this._exOp(':'); elseBranch = this._parseBlock(); }
    return { type: 'while', cond, body, else: elseBranch, ln };
  }

  _parseFor() {
    const ln = this._nx().ln;
    const targetFirst = this._parsePrimaryTarget();
    let target = targetFirst;
    if (this._pk().t === 'op' && this._pk().v === ',') {
      const items = [targetFirst];
      while (this._pk().t === 'op' && this._pk().v === ',') { this._nx(); if (this._isKw('in')) break; items.push(this._parsePrimaryTarget()); }
      target = { type: 'tuple', items };
    }
    if (!this._isKw('in')) throw new Error(`Expected 'in' in for-loop near line ${this._pk().ln}`);
    this._nx();
    const iter = this._parseExpr();
    this._exOp(':');
    const body = this._parseBlock();
    let elseBranch = null;
    this._skipNL();
    if (this._isKw('else')) { this._nx(); this._exOp(':'); elseBranch = this._parseBlock(); }
    return { type: 'for', target, iter, body, else: elseBranch, ln };
  }
  _parsePrimaryTarget() { const t = this._nx(); return { type: 'id', n: t.v, ln: t.ln }; }

  _parseDef() {
    const ln = this._nx().ln;
    const name = this._nx().v;
    this._exOp('(');
    const params = [];
    while (this._pk().t !== 'eof' && !(this._pk().t === 'op' && this._pk().v === ')')) {
      if (this._pk().t === 'op' && this._pk().v === ',') { this._nx(); continue; }
      const pname = this._nx().v;
      let def = null;
      if (this._pk().t === 'op' && this._pk().v === '=') { this._nx(); def = this._parseExpr(); }
      params.push({ name: pname, def });
    }
    this._exOp(')');
    this._exOp(':');
    const body = this._parseBlock();
    return { type: 'def', name, params, body, ln };
  }

  _parseReturn() {
    const ln = this._nx().ln;
    let val = null;
    if (this._pk().t !== 'NEWLINE' && this._pk().t !== 'eof' && this._pk().t !== 'DEDENT') val = this._parseExprList();
    this._skipNL();
    return { type: 'return', val, ln };
  }

  _parseExpr() { return this._parseTernary(); }
  _parseTernary() {
    const e = this._parseOr();
    if (this._isKw('if')) {
      this._nx();
      const cond = this._parseOr();
      if (!this._isKw('else')) throw new Error(`Expected 'else' in conditional expression near line ${this._pk().ln}`);
      this._nx();
      const elseE = this._parseTernary();
      return { type: 'ifexp', cond, then: e, else: elseE };
    }
    return e;
  }
  _parseOr() { let e = this._parseAnd(); while (this._isKw('or')) { this._nx(); e = { type: 'bin', op: 'or', l: e, r: this._parseAnd() }; } return e; }
  _parseAnd() { let e = this._parseNot(); while (this._isKw('and')) { this._nx(); e = { type: 'bin', op: 'and', l: e, r: this._parseNot() }; } return e; }
  _parseNot() { if (this._isKw('not')) { this._nx(); return { type: 'un', op: 'not', x: this._parseNot() }; } return this._parseComparison(); }
  _parseComparison() {
    let e = this._parseAddSub();
    while (true) {
      const t = this._pk();
      if (t.t === 'op' && ['==', '!=', '<', '>', '<=', '>='].includes(t.v)) { this._nx(); e = { type: 'bin', op: t.v, l: e, r: this._parseAddSub() }; continue; }
      if (t.t === 'id' && t.v === 'in') { this._nx(); e = { type: 'bin', op: 'in', l: e, r: this._parseAddSub() }; continue; }
      if (t.t === 'id' && t.v === 'not' && this._pk(1).t === 'id' && this._pk(1).v === 'in') { this._nx(); this._nx(); e = { type: 'bin', op: 'notin', l: e, r: this._parseAddSub() }; continue; }
      if (t.t === 'id' && t.v === 'is') { this._nx(); let op = 'is'; if (this._isKw('not')) { this._nx(); op = 'isnot'; } e = { type: 'bin', op, l: e, r: this._parseAddSub() }; continue; }
      break;
    }
    return e;
  }
  _parseAddSub() { let e = this._parseMulDiv(); while (this._pk().t === 'op' && (this._pk().v === '+' || this._pk().v === '-')) { const op = this._nx().v; e = { type: 'bin', op, l: e, r: this._parseMulDiv() }; } return e; }
  _parseMulDiv() { let e = this._parseUnary(); while (this._pk().t === 'op' && ['*', '/', '//', '%'].includes(this._pk().v)) { const op = this._nx().v; e = { type: 'bin', op, l: e, r: this._parseUnary() }; } return e; }
  _parseUnary() {
    if (this._pk().t === 'op' && this._pk().v === '-') { this._nx(); return { type: 'un', op: '-', x: this._parseUnary() }; }
    if (this._pk().t === 'op' && this._pk().v === '+') { this._nx(); return this._parseUnary(); }
    return this._parsePow();
  }
  _parsePow() { const e = this._parsePostfix(); if (this._pk().t === 'op' && this._pk().v === '**') { this._nx(); return { type: 'bin', op: '**', l: e, r: this._parseUnary() }; } return e; }

  _parsePostfix() {
    let e = this._parsePrimary();
    while (true) {
      const t = this._pk();
      if (t.t === 'op' && t.v === '(') {
        this._nx();
        const args = [];
        const kwargs = [];
        while (!(this._pk().t === 'op' && this._pk().v === ')')) {
          if (this._pk().t === 'op' && this._pk().v === ',') { this._nx(); continue; }
          if (this._pk().t === 'id' && this._pk(1).t === 'op' && this._pk(1).v === '=') {
            const kwName = this._nx().v;
            this._nx();
            const kwVal = this._parseExpr();
            kwargs.push({ name: kwName, value: kwVal });
            continue;
          }
          args.push(this._parseExpr());
        }
        this._exOp(')');
        e = { type: 'call', fn: e, args, kwargs, ln: t.ln };
        continue;
      }
      if (t.t === 'op' && t.v === '[') {
        this._nx();
        let a = null, b = null, isSlice = false;
        if (!(this._pk().t === 'op' && this._pk().v === ':')) a = this._parseExpr();
        if (this._pk().t === 'op' && this._pk().v === ':') {
          isSlice = true; this._nx();
          if (!(this._pk().t === 'op' && this._pk().v === ']')) b = this._parseExpr();
        }
        this._exOp(']');
        e = isSlice ? { type: 'slice', x: e, a, b, ln: t.ln } : { type: 'sub', x: e, i: a, ln: t.ln };
        continue;
      }
      if (t.t === 'op' && t.v === '.') { this._nx(); const name = this._nx().v; e = { type: 'attr', x: e, name, ln: t.ln }; continue; }
      break;
    }
    return e;
  }

  _parsePrimary() {
    const t = this._nx();
    if (t.t === 'num') return { type: 'lit', v: t.v, isFloat: !!t.isFloat, ln: t.ln };
    if (t.t === 'str') return { type: 'slit', v: t.v, ln: t.ln };
    if (t.t === 'fstr') return { type: 'fstr', v: t.v, ln: t.ln };
    if (t.t === 'id') {
      if (t.v === 'True') return { type: 'lit', v: true, ln: t.ln };
      if (t.v === 'False') return { type: 'lit', v: false, ln: t.ln };
      if (t.v === 'None') return { type: 'lit', v: null, ln: t.ln };
      return { type: 'id', n: t.v, ln: t.ln };
    }
    if (t.t === 'op' && t.v === '(') {
      if (this._pk().t === 'op' && this._pk().v === ')') { this._nx(); return { type: 'tuple', items: [], ln: t.ln }; }
      const first = this._parseExpr();
      if (this._pk().t === 'op' && this._pk().v === ',') {
        const items = [first];
        while (this._pk().t === 'op' && this._pk().v === ',') { this._nx(); if (this._pk().t === 'op' && this._pk().v === ')') break; items.push(this._parseExpr()); }
        this._exOp(')');
        return { type: 'tuple', items, ln: t.ln };
      }
      this._exOp(')');
      return first;
    }
    if (t.t === 'op' && t.v === '[') {
      const items = [];
      while (!(this._pk().t === 'op' && this._pk().v === ']')) { if (this._pk().t === 'op' && this._pk().v === ',') { this._nx(); continue; } items.push(this._parseExpr()); }
      this._exOp(']');
      return { type: 'list', items, ln: t.ln };
    }
    if (t.t === 'op' && t.v === '{') {
      const items = []; let isSet = false;
      while (!(this._pk().t === 'op' && this._pk().v === '}')) {
        if (this._pk().t === 'op' && this._pk().v === ',') { this._nx(); continue; }
        const k = this._parseExpr();
        if (this._pk().t === 'op' && this._pk().v === ':') { this._nx(); const v = this._parseExpr(); items.push([k, v]); }
        else { isSet = true; items.push([k, k]); }
      }
      this._exOp('}');
      return { type: isSet ? 'set' : 'dict', items, ln: t.ln };
    }
    return { type: 'lit', v: 0, ln: t.ln };
  }

  _run(prog) {
    this._addStep({ ln: 1, desc: 'Program starts.', frames: [], heap: {}, out: '', cs: [] });
    for (const s of prog) if (s.type === 'def') this.functions[s.name] = s;
    try { this._execBlock(prog.filter(s => s.type !== 'def'), this._globalFrame); }
    catch (e) { if (!(e && (e.type === 'ret' || e.type === 'break' || e.type === 'cont'))) throw e; }
    this._addStep({ ln: 1, desc: '<b>Program finished executing.</b>', frames: this._snapFrames(), heap: this._snapHeap(), out: this.output, cs: [] });
  }

  _callFn(name, args, kwargs, callLn) {
    const fn = this.functions[name];
    if (!fn) throw new Error(`NameError: name '${name}' is not defined (line ${callLn || '?'})`);
    const frame = { name, vars: {} };
    fn.params.forEach((p, i) => {
      let v;
      if (i < args.length) v = args[i];
      else if (kwargs && kwargs[p.name] !== undefined) v = kwargs[p.name];
      else if (p.def) v = this._eval(p.def, this._globalFrame);
      else v = null;
      frame.vars[p.name] = { value: v, changed: true };
    });
    this._callStack.push(frame);
    if (this._callStack.length > 300) throw new Error(`RecursionError: maximum recursion depth exceeded in ${name}()`);
    this._addStep({ ln: fn.ln, desc: `Called <b>${name}(${args.map(a => this._fv(a)).join(', ')})</b>`, frames: this._snapFrames(), heap: this._snapHeap(), out: this.output, cs: this._callStack.map(f => f.name) });
    let ret;
    try { this._execBlock(fn.body, frame); ret = null; }
    catch (e) { if (e && e.type === 'ret') ret = e.val === undefined ? null : e.val; else throw e; }
    this._callStack.pop();
    this._addStep({ ln: callLn || fn.ln, desc: `<b>${name}()</b> returned ${this._fv(ret)}`, frames: this._snapFrames(), heap: this._snapHeap(), out: this.output, cs: this._callStack.map(f => f.name) });
    return ret;
  }

  _execBlock(stmts, frame) { for (const s of stmts) this._execStmt(s, frame); }

  _execStmt(s, frame) {
    switch (s.type) {
      case 'pass': return;
      case 'def': this.functions[s.name] = s; return;
      case 'assign': return this._execAssign(s, frame);
      case 'expr': { this._eval(s.expr, frame); return; }
      case 'return': {
        const v = s.val ? this._eval(s.val, frame) : null;
        this._addStep({ ln: s.ln, desc: `return <b>${this._fv(v)}</b>`, frames: this._snapFrames(), heap: this._snapHeap(), out: this.output, cs: this._callStack.map(f => f.name) });
        throw { type: 'ret', val: v };
      }
      case 'break': throw { type: 'break' };
      case 'continue': throw { type: 'cont' };
      case 'if': return this._execIf(s, frame);
      case 'while': return this._execWhile(s, frame);
      case 'for': return this._execFor(s, frame);
    }
  }

  _execAssign(s, frame) {
    let rhs = this._eval(s.value, frame);
    if (s.op !== '=') { const cur = this._eval(s.target, frame); rhs = this._applyAug(s.op, cur, rhs); }
    this._assignTo(s.target, rhs, frame);
    const nm = this._exprName(s.target);
    const step = { ln: s.ln, desc: `Assign <code>${nm}</code> ${s.op} &rarr; <b>${this._fv(rhs)}</b>`, frames: this._snapFrames(), heap: this._snapHeap(), out: this.output, cs: this._callStack.map(f => f.name), chg: nm };
    if (s.target.type === 'sub') {
      try {
        const base = this._eval(s.target.x, frame);
        const idx = this._eval(s.target.i, frame);
        if (typeof base === 'string' && this._heap[base]) {
          const o = this._heap[base];
          const i2 = (typeof idx === 'number' && idx < 0) ? o.items.length + idx : idx;
          step.writeAddr = base; step.writeIdx = i2;
        }
      } catch (e) { /* best-effort highlight only */ }
    }
    this._addStep(step);
  }
  _applyAug(op, cur, rhs) {
    switch (op) {
      case '+=': return (typeof cur === 'string' || typeof rhs === 'string') ? String(cur) + String(rhs) : cur + rhs;
      case '-=': return cur - rhs;
      case '*=': return cur * rhs;
      case '/=': return cur / rhs;
      case '//=': return Math.floor(cur / rhs);
      case '%=': return ((cur % rhs) + rhs) % rhs;
      case '**=': return Math.pow(cur, rhs);
    }
    return rhs;
  }

  _assignTo(target, val, frame) {
    if (target.type === 'tuple') { const arr = this._toArray(val); target.items.forEach((it, i) => this._assignTo(it, arr[i], frame)); return; }
    if (target.type === 'id') {
      const cur = this._findVarFrame(target.n, frame);
      if (cur) { cur.vars[target.n].value = val; cur.vars[target.n].changed = true; }
      else frame.vars[target.n] = { value: val, changed: true };
      return;
    }
    if (target.type === 'sub') {
      const base = this._eval(target.x, frame);
      const idx = this._eval(target.i, frame);
      const obj = this._heap[base];
      if (obj && obj.kind === 'list') { const i2 = idx < 0 ? obj.items.length + idx : idx; obj.items[i2] = val; }
      else if (obj && obj.kind === 'dict') { const found = obj.items.find(([k]) => this._pyEq(k, idx)); if (found) found[1] = val; else obj.items.push([idx, val]); }
      return;
    }
    if (target.type === 'attr') {
      const base = this._eval(target.x, frame);
      const obj = this._heap[base];
      if (obj) { obj.attrs = obj.attrs || {}; obj.attrs[target.name] = val; }
      return;
    }
  }
  _findVarFrame(name, frame) {
    if (frame && frame.vars && frame.vars[name] !== undefined) return frame;
    if (frame && frame.isGlobal) return null;
    if (this._globalFrame.vars[name] !== undefined) return this._globalFrame;
    return null;
  }
  _toArray(v) {
    if (v && v.__tuple) return v.items;
    if (Array.isArray(v)) return v;
    if (typeof v === 'string' && this._heap[v] && this._heap[v].kind === 'list') return this._heap[v].items;
    return [v];
  }
  _exprName(e) {
    if (!e) return '?';
    if (e.type === 'id') return e.n;
    if (e.type === 'tuple') return e.items.map(i => this._exprName(i)).join(', ');
    if (e.type === 'sub') return this._exprName(e.x) + '[...]';
    if (e.type === 'attr') return this._exprName(e.x) + '.' + e.name;
    return '?';
  }

  _execIf(s, frame) {
    const c = this._truthy(this._eval(s.cond, frame));
    this._addStep({ ln: s.ln, part: 'cond', desc: `<b>if</b> condition is <b>${c ? 'True ✓' : 'False ✗'}</b>`, frames: this._snapFrames(), heap: this._snapHeap(), out: this.output, cs: this._callStack.map(f => f.name) });
    if (c) this._execBlock(s.then, frame); else if (s.else) this._execBlock(s.else, frame);
  }

  _execWhile(s, frame) {
    let iter = 0;
    while (iter++ < 5000) {
      const c = this._truthy(this._eval(s.cond, frame));
      this._addStep({ ln: s.ln, part: 'cond', desc: `<b>while</b> condition is <b>${c ? 'True ✓' : 'False ✗'}</b>`, frames: this._snapFrames(), heap: this._snapHeap(), out: this.output, cs: this._callStack.map(f => f.name) });
      if (!c) { if (s.else) this._execBlock(s.else, frame); break; }
      try { this._execBlock(s.body, frame); } catch (e) { if (e.type === 'break') break; if (e.type !== 'cont') throw e; }
    }
  }

  _iterate(v) {
    if (typeof v === 'string' && this._heap[v]) {
      const o = this._heap[v];
      if (o.kind === 'list' || o.kind === 'set') return o.items.slice();
      if (o.kind === 'dict') return o.items.map(([k]) => k);
    }
    if (typeof v === 'string') return v.split('');
    if (v && v.__range) { const out = []; for (let x = v.start; v.step > 0 ? x < v.stop : x > v.stop; x += v.step) out.push(x); return out; }
    if (v && v.__tuple) return v.items.slice();
    if (Array.isArray(v)) return v.slice();
    return [];
  }

  _execFor(s, frame) {
    const items = this._iterate(this._eval(s.iter, frame));
    let broke = false;
    for (const it of items) {
      this._assignTo(s.target, it, frame);
      this._addStep({ ln: s.ln, part: 'for-assign', desc: `<b>for</b> ${this._exprName(s.target)} = <b>${this._fv(it)}</b>`, frames: this._snapFrames(), heap: this._snapHeap(), out: this.output, cs: this._callStack.map(f => f.name), chg: this._exprName(s.target) });
      try { this._execBlock(s.body, frame); } catch (e) { if (e.type === 'break') { broke = true; break; } if (e.type !== 'cont') throw e; }
    }
    if (!broke && s.else) this._execBlock(s.else, frame);
  }

  _truthy(v) {
    if (v === null || v === undefined || v === false) return false;
    if (typeof v === 'string') return v.length > 0;
    if (typeof v === 'number') return v !== 0;
    if (typeof v === 'boolean') return v;
    if (v && v.__tuple) return v.items.length > 0;
    if (typeof v === 'string' && this._heap[v]) return this._heap[v].items.length > 0;
    return !!v;
  }

  _lookup(name, frame) {
    if (frame && frame.vars && frame.vars[name] !== undefined) return frame.vars[name].value;
    if (this._globalFrame.vars[name] !== undefined) return this._globalFrame.vars[name].value;
    if (this.functions[name]) return { __func: name };
    throw new Error(`NameError: name '${name}' is not defined`);
  }

  _eval(e, frame) {
    if (!e) return null;
    switch (e.type) {
      case 'lit': return e.v;
      case 'slit': return e.v;
      case 'fstr': return this._evalFString(e.v, frame);
      case 'id': return this._lookup(e.n, frame);
      case 'list': { const items = e.items.map(it => this._eval(it, frame)); const addr = this._heapAddr(); this._heap[addr] = { kind: 'list', items }; return addr; }
      case 'dict': { const items = e.items.map(([k, v]) => [this._eval(k, frame), this._eval(v, frame)]); const addr = this._heapAddr(); this._heap[addr] = { kind: 'dict', items }; return addr; }
      case 'set': { const items = e.items.map(([k]) => this._eval(k, frame)); const addr = this._heapAddr(); this._heap[addr] = { kind: 'set', items: items.map(v => [v, v]) }; return addr; }
      case 'tuple': return { __tuple: true, items: e.items.map(it => this._eval(it, frame)) };
      case 'ifexp': return this._truthy(this._eval(e.cond, frame)) ? this._eval(e.then, frame) : this._eval(e.else, frame);
      case 'un': { const v = this._eval(e.x, frame); if (e.op === '-') return -v; if (e.op === 'not') return !this._truthy(v); return v; }
      case 'bin': return this._evalBin(e, frame);
      case 'sub': {
        const base = this._eval(e.x, frame); const idx = this._eval(e.i, frame);
        if (typeof base === 'string' && this._heap[base]) {
          const o = this._heap[base];
          if (o.kind === 'list') {
            if (typeof idx !== 'number') throw new Error(`TypeError: list indices must be integers or slices, not ${typeof idx === 'string' ? 'str' : typeof idx}`);
            const i2 = idx < 0 ? o.items.length + idx : idx;
            if (i2 < 0 || i2 >= o.items.length) throw new Error(`IndexError: list index out of range`);
            return o.items[i2];
          }
          if (o.kind === 'dict') { const f2 = o.items.find(([k]) => this._pyEq(k, idx)); if (!f2) throw new Error(`KeyError: ${this._fv(idx)}`); return f2[1]; }
        }
        if (typeof base === 'string') { const i2 = idx < 0 ? base.length + idx : idx; return base[i2]; }
        if (base && base.__tuple) { const i2 = idx < 0 ? base.items.length + idx : idx; return base.items[i2]; }
        return null;
      }
      case 'slice': {
        const base = this._eval(e.x, frame);
        const arr = this._sliceSrc(base);
        const len = arr.length;
        let a = e.a ? this._eval(e.a, frame) : 0;
        let b = e.b ? this._eval(e.b, frame) : len;
        if (a < 0) a = Math.max(0, len + a);
        if (b < 0) b = Math.max(0, len + b);
        const out = arr.slice(a, b);
        if (typeof base === 'string' && !this._heap[base]) return out.join('');
        const addr = this._heapAddr(); this._heap[addr] = { kind: 'list', items: out }; return addr;
      }
      case 'attr': return { __bound: true, base: this._eval(e.x, frame), name: e.name };
      case 'call': return this._evalCall(e, frame);
      default: return null;
    }
  }
  _sliceSrc(base) {
    if (typeof base === 'string' && this._heap[base]) return this._heap[base].items;
    if (typeof base === 'string') return base.split('');
    if (base && base.__tuple) return base.items;
    return [];
  }

  _pyEq(a, b) { if (a === b) return true; if (typeof a === 'number' && typeof b === 'number') return a === b; return JSON.stringify(a) === JSON.stringify(b); }

  _evalBin(e, frame) {
    if (e.op === 'and') { const l = this._eval(e.l, frame); return this._truthy(l) ? this._eval(e.r, frame) : l; }
    if (e.op === 'or') { const l = this._eval(e.l, frame); return this._truthy(l) ? l : this._eval(e.r, frame); }
    const l = this._eval(e.l, frame), r = this._eval(e.r, frame);
    switch (e.op) {
      case '+':
        if (typeof l === 'string' && typeof r === 'string' && !this._heap[l] && !this._heap[r]) return l + r;
        if (typeof l === 'string' && this._heap[l] && this._heap[l].kind === 'list' && typeof r === 'string' && this._heap[r] && this._heap[r].kind === 'list') {
          const addr = this._heapAddr(); this._heap[addr] = { kind: 'list', items: [...this._heap[l].items, ...this._heap[r].items] }; return addr;
        }
        return l + r;
      case '-': return l - r;
      case '*':
        if (typeof l === 'string' && typeof r === 'number' && !this._heap[l]) return l.repeat(Math.max(0, r));
        if (typeof r === 'string' && typeof l === 'number' && !this._heap[r]) return r.repeat(Math.max(0, l));
        return l * r;
      case '/': return l / r;
      case '//': return Math.floor(l / r);
      case '%': if (typeof l === 'string') return this._pyFormat(l, Array.isArray(r) ? r : (r && r.__tuple ? r.items : [r])); return ((l % r) + r) % r;
      case '**': return Math.pow(l, r);
      case '==': return this._pyEq(l, r);
      case '!=': return !this._pyEq(l, r);
      case '<': return l < r; case '>': return l > r;
      case '<=': return l <= r; case '>=': return l >= r;
      case 'in': return this._containsCheck(l, r);
      case 'notin': return !this._containsCheck(l, r);
      case 'is': return l === r; case 'isnot': return l !== r;
      default: return null;
    }
  }
  _containsCheck(needle, hay) {
    if (typeof hay === 'string' && this._heap[hay]) {
      const o = this._heap[hay];
      if (o.kind === 'dict') return o.items.some(([k]) => this._pyEq(k, needle));
      return o.items.some(v => this._pyEq(v, needle));
    }
    if (typeof hay === 'string') return hay.includes(String(needle));
    if (hay && hay.__tuple) return hay.items.some(v => this._pyEq(v, needle));
    return false;
  }
  _pyFormat(fmt, args) { let i = 0; return fmt.replace(/%[sd]/g, () => String(args[i++])); }

  _evalFString(raw, frame) {
    let out = '', i = 0;
    while (i < raw.length) {
      if (raw[i] === '{' && raw[i + 1] !== '{') {
        let depth = 1, j = i + 1;
        while (j < raw.length && depth > 0) { if (raw[j] === '{') depth++; else if (raw[j] === '}') depth--; if (depth > 0) j++; }
        out += this._fv(this._evalSubExpr(raw.slice(i + 1, j), frame));
        i = j + 1;
      } else if (raw[i] === '{' && raw[i + 1] === '{') { out += '{'; i += 2; }
      else if (raw[i] === '}' && raw[i + 1] === '}') { out += '}'; i += 2; }
      else { out += raw[i]; i++; }
    }
    return out;
  }
  _evalSubExpr(src, frame) {
    const saveTokens = this.tokens, saveTi = this._ti;
    try { const tmp = this._tokenizeString(src); this.tokens = tmp; this._ti = 0; const node = this._parseExpr(); return this._eval(node, frame); }
    finally { this.tokens = saveTokens; this._ti = saveTi; }
  }
  _tokenizeString(src) {
    const savedCode = this.code, savedTokens = this.tokens;
    this.code = src; this._tokenize();
    const toks = this.tokens;
    this.code = savedCode; this.tokens = savedTokens;
    return toks;
  }

  get _builtins() {
    if (!this.__b) this.__b = new Set(['print', 'len', 'range', 'int', 'str', 'float', 'bool', 'abs', 'min', 'max', 'sum', 'round', 'sorted', 'list', 'dict', 'input', 'type', 'enumerate', 'reversed', 'zip']);
    return this.__b;
  }

  _evalCall(e, frame) {
    const args = e.args.map(a => this._eval(a, frame));
    const kwargs = {};
    if (e.kwargs) e.kwargs.forEach(k => { kwargs[k.name] = this._eval(k.value, frame); });
    const ln = e.ln;
    if (e.fn.type === 'attr') {
      const base = this._eval(e.fn.x, frame);
      const res = this._callMethod(base, e.fn.name, args, kwargs);
      this._addStep({ ln, desc: `<code>${this._exprName(e.fn.x)}.${e.fn.name}(${args.map(a => this._fv(a)).join(', ')})</code> called`, frames: this._snapFrames(), heap: this._snapHeap(), out: this.output, cs: this._callStack.map(f => f.name) });
      return res;
    }
    const fnName = e.fn.type === 'id' ? e.fn.n : null;
    if (fnName && this._builtins.has(fnName)) return this._callBuiltin(fnName, args, ln, kwargs);
    if (fnName && this.functions[fnName]) {
      this._addStep({ ln, desc: `About to call <b>${fnName}(${args.map(a => this._fv(a)).join(', ')})</b>`, frames: this._snapFrames(), heap: this._snapHeap(), out: this.output, cs: this._callStack.map(f => f.name) });
      return this._callFn(fnName, args, kwargs, ln);
    }
    const fv = this._eval(e.fn, frame);
    if (fv && fv.__func) return this._callFn(fv.__func, args, kwargs, ln);
    throw new Error(`TypeError: '${fnName || this._exprName(e.fn)}' is not callable (line ${ln})`);
  }

  _callBuiltin(name, args, ln, kwargs) {
    kwargs = kwargs || {};
    switch (name) {
      case 'print': {
        const sep = kwargs.sep !== undefined ? String(kwargs.sep) : ' ';
        const end = kwargs.end !== undefined ? String(kwargs.end) : '\n';
        const s = args.map(a => this._fv(a)).join(sep) + end;
        this.output += s;
        this._addStep({ ln, desc: `<code>print</code>: <b>"${s.replace(/\n/g, '↵').replace(/</g, '&lt;').slice(0, 100)}"</b>`, frames: this._snapFrames(), heap: this._snapHeap(), out: this.output, cs: this._callStack.map(f => f.name) });
        return null;
      }
      case 'len': {
        const v = args[0];
        if (typeof v === 'string' && this._heap[v]) return this._heap[v].items.length;
        if (typeof v === 'string') return v.length;
        if (v && v.__tuple) return v.items.length;
        return 0;
      }
      case 'range': {
        let start = 0, stop = 0, step = 1;
        if (args.length === 1) stop = args[0];
        else if (args.length === 2) { start = args[0]; stop = args[1]; }
        else { start = args[0]; stop = args[1]; step = args[2]; }
        return { __range: true, start, stop, step };
      }
      case 'int': return args.length ? Math.trunc(typeof args[0] === 'string' ? (parseInt(args[0], 10) || 0) : args[0]) : 0;
      case 'float': return args.length ? (typeof args[0] === 'string' ? (parseFloat(args[0]) || 0) : Number(args[0])) : 0.0;
      case 'str': return args.length ? this._fv(args[0]) : '';
      case 'bool': return args.length ? this._truthy(args[0]) : false;
      case 'abs': return Math.abs(args[0]);
      case 'round': return args.length > 1 ? Math.round(args[0] * Math.pow(10, args[1])) / Math.pow(10, args[1]) : Math.round(args[0]);
      case 'min': { const arr = args.length === 1 ? this._iterate(args[0]) : args; return arr.reduce((a, b) => (b < a ? b : a)); }
      case 'max': { const arr = args.length === 1 ? this._iterate(args[0]) : args; return arr.reduce((a, b) => (b > a ? b : a)); }
      case 'sum': { const arr = this._iterate(args[0]); const start = args[1] || 0; return arr.reduce((a, b) => a + b, start); }
      case 'sorted': { const arr = this._iterate(args[0]).slice(); arr.sort((a, b) => a < b ? -1 : a > b ? 1 : 0); const addr = this._heapAddr(); this._heap[addr] = { kind: 'list', items: arr }; return addr; }
      case 'list': { const items = args.length ? this._iterate(args[0]) : []; const addr = this._heapAddr(); this._heap[addr] = { kind: 'list', items: items.slice() }; return addr; }
      case 'dict': { const addr = this._heapAddr(); this._heap[addr] = { kind: 'dict', items: [] }; return addr; }
      case 'type': {
        const v = args[0];
        if (typeof v === 'number') return Number.isInteger(v) ? "<class 'int'>" : "<class 'float'>";
        if (typeof v === 'string' && this._heap[v]) return `<class '${this._heap[v].kind}'>`;
        if (typeof v === 'string') return "<class 'str'>";
        if (typeof v === 'boolean') return "<class 'bool'>";
        if (v === null) return "<class 'NoneType'>";
        return "<class 'object'>";
      }
      case 'enumerate': { const arr = this._iterate(args[0]); const start = args[1] || 0; const addr = this._heapAddr(); this._heap[addr] = { kind: 'list', items: arr.map((v, i) => ({ __tuple: true, items: [i + start, v] })) }; return addr; }
      case 'reversed': { const arr = this._iterate(args[0]).slice().reverse(); const addr = this._heapAddr(); this._heap[addr] = { kind: 'list', items: arr }; return addr; }
      case 'zip': { const arrs = args.map(a => this._iterate(a)); const n = Math.min(...arrs.map(a => a.length)); const out = []; for (let i = 0; i < n; i++) out.push({ __tuple: true, items: arrs.map(a => a[i]) }); const addr = this._heapAddr(); this._heap[addr] = { kind: 'list', items: out }; return addr; }
      case 'input': {
        let raw;
        if (this._stdinIdx < this.stdinQueue.length) raw = String(this.stdinQueue[this._stdinIdx++]);
        else { const p = (typeof window !== 'undefined' && window.prompt) ? window.prompt('Program needs input:', '') : ''; raw = p === null ? '' : p; this.stdinQueue.push(raw); this._stdinIdx++; }
        this.output += raw + '\n';
        this._addStep({ ln, desc: `<code>input()</code> &rarr; <b>"${raw}"</b>`, frames: this._snapFrames(), heap: this._snapHeap(), out: this.output, cs: this._callStack.map(f => f.name) });
        return raw;
      }
    }
    return null;
  }

  _callMethod(base, name, args) {
    if (typeof base === 'string' && this._heap[base]) {
      const o = this._heap[base];
      if (o.kind === 'list') {
        switch (name) {
          case 'append': o.items.push(args[0]); return null;
          case 'pop': { const i = args.length ? args[0] : o.items.length - 1; const i2 = i < 0 ? o.items.length + i : i; return o.items.splice(i2, 1)[0]; }
          case 'insert': o.items.splice(args[0], 0, args[1]); return null;
          case 'remove': { const i = o.items.findIndex(v => this._pyEq(v, args[0])); if (i >= 0) o.items.splice(i, 1); return null; }
          case 'sort': o.items.sort((a, b) => a < b ? -1 : a > b ? 1 : 0); if (args.length && args[0]) o.items.reverse(); return null;
          case 'reverse': o.items.reverse(); return null;
          case 'index': return o.items.findIndex(v => this._pyEq(v, args[0]));
          case 'count': return o.items.filter(v => this._pyEq(v, args[0])).length;
          case 'clear': o.items.length = 0; return null;
          case 'copy': { const addr = this._heapAddr(); this._heap[addr] = { kind: 'list', items: o.items.slice() }; return addr; }
          case 'extend': o.items.push(...this._iterate(args[0])); return null;
        }
      }
      if (o.kind === 'dict') {
        switch (name) {
          case 'get': { const f2 = o.items.find(([k]) => this._pyEq(k, args[0])); return f2 ? f2[1] : (args.length > 1 ? args[1] : null); }
          case 'keys': { const addr = this._heapAddr(); this._heap[addr] = { kind: 'list', items: o.items.map(([k]) => k) }; return addr; }
          case 'values': { const addr = this._heapAddr(); this._heap[addr] = { kind: 'list', items: o.items.map(([, v]) => v) }; return addr; }
          case 'items': { const addr = this._heapAddr(); this._heap[addr] = { kind: 'list', items: o.items.map(([k, v]) => ({ __tuple: true, items: [k, v] })) }; return addr; }
          case 'pop': { const i = o.items.findIndex(([k]) => this._pyEq(k, args[0])); if (i >= 0) return o.items.splice(i, 1)[0][1]; return args.length > 1 ? args[1] : null; }
          case 'update': { const src = this._heap[args[0]]; if (src) src.items.forEach(([k, v]) => { const f2 = o.items.find(([k2]) => this._pyEq(k2, k)); if (f2) f2[1] = v; else o.items.push([k, v]); }); return null; }
        }
      }
    }
    if (typeof base === 'string' && !this._heap[base]) {
      switch (name) {
        case 'upper': return base.toUpperCase();
        case 'lower': return base.toLowerCase();
        case 'strip': return base.trim();
        case 'lstrip': return base.replace(/^\s+/, '');
        case 'rstrip': return base.replace(/\s+$/, '');
        case 'split': { const sep = args.length ? args[0] : /\s+/; const parts = base.split(sep).filter(x => args.length ? true : x !== ''); const addr = this._heapAddr(); this._heap[addr] = { kind: 'list', items: parts }; return addr; }
        case 'join': { const arr = this._iterate(args[0]); return arr.map(v => this._fv(v)).join(base); }
        case 'replace': return base.split(args[0]).join(args[1]);
        case 'startswith': return base.startsWith(args[0]);
        case 'endswith': return base.endsWith(args[0]);
        case 'find': return base.indexOf(args[0]);
        case 'count': return base.split(args[0]).length - 1;
        case 'title': return base.replace(/\w\S*/g, t => t[0].toUpperCase() + t.slice(1).toLowerCase());
        case 'capitalize': return base.length ? base[0].toUpperCase() + base.slice(1).toLowerCase() : base;
        case 'format': { let i = 0; return base.replace(/\{\}/g, () => this._fv(args[i++])); }
        case 'isdigit': return /^\d+$/.test(base);
        case 'isalpha': return /^[a-zA-Z]+$/.test(base);
      }
    }
    throw new Error(`AttributeError: object has no method '${name}'`);
  }

  _fv(v) {
    if (v === null || v === undefined) return 'None';
    if (v === true) return 'True';
    if (v === false) return 'False';
    if (typeof v === 'number') return String(v);
    if (typeof v === 'string' && this._heap[v]) return this._heapRepr(v, new Set());
    if (typeof v === 'string') return v;
    if (v && v.__tuple) return '(' + v.items.map(x => this._fv(x)).join(', ') + (v.items.length === 1 ? ',' : '') + ')';
    if (v && v.__range) return `range(${v.start}, ${v.stop}${v.step !== 1 ? ', ' + v.step : ''})`;
    if (v && v.__func) return `<function ${v.__func}>`;
    return String(v);
  }
  _heapRepr(addr, seen) {
    if (seen.has(addr)) return '[...]';
    seen.add(addr);
    const o = this._heap[addr];
    if (!o) return 'None';
    if (o.kind === 'list' || o.kind === 'set') {
      const inner = o.items.map(x => (typeof x === 'string' && this._heap[x]) ? this._heapRepr(x, seen) : this._fv(x)).join(', ');
      return o.kind === 'set' ? `{${inner}}` : `[${inner}]`;
    }
    if (o.kind === 'dict') {
      const inner = o.items.map(([k, v]) => `${this._fv(k)}: ${(typeof v === 'string' && this._heap[v]) ? this._heapRepr(v, seen) : this._fv(v)}`).join(', ');
      return `{${inner}}`;
    }
    return 'None';
  }

  _snapFrames() {
    const fs = [];
    for (const f of this._callStack) {
      const vars = {};
      for (const [k, v] of Object.entries(f.vars)) vars[k] = { value: v.value, changed: !!v.changed };
      fs.push({ name: f.name, vars, isActive: true });
    }
    if (Object.keys(this._globalFrame.vars).length) {
      const gv = {};
      for (const [k, v] of Object.entries(this._globalFrame.vars)) gv[k] = { value: v.value, changed: !!v.changed };
      fs.unshift({ name: '[Global]', vars: gv, isActive: this._callStack.length === 0 });
    }
    return fs;
  }
  _snapHeap() {
    const h = {};
    for (const [addr, o] of Object.entries(this._heap)) h[addr] = { kind: o.kind, items: (o.items || []).map(x => Array.isArray(x) ? x.slice() : x) };
    return h;
  }

  _addStep(s) { if (this.steps.length < 6000) this.steps.push(s); }
}

/* =========================================================================
   SAMPLES
   ========================================================================= */
const SAMPLES = {
hello: `print("Hello, World!")
print("Welcome to Python Visualizer Plus!")`,

variables: `age = 30
pi = 3.14
grade = "A"
is_active = True
nothing = None
print(age, pi, grade, is_active, nothing)`,

arithmetic: `a = 15
b = 4
print(a + b)
print(a - b)
print(a * b)
print(a / b)
print(a // b)
print(a % b)
print(a ** 2)`,

fstrings: `name = "Anisur"
age = 30
gpa = 3.85
print(f"My name is {name}, I am {age} years old.")
print(f"GPA rounded: {round(gpa, 1)}")`,

input_add: `num1 = int(input("Enter first number: "))
num2 = int(input("Enter second number: "))
total = num1 + num2
print("Sum:", total)`,

if_else: `score = 75
if score >= 90:
    grade = "A"
elif score >= 80:
    grade = "B"
elif score >= 70:
    grade = "C"
else:
    grade = "F"
print("Score:", score)
print("Grade:", grade)`,

for_loop: `for i in range(1, 11):
    print(i)
    
fruits = ["apple", "banana ", "cherry"]
for i in fruits:
    print(i)`,

nested_loop: `n = 5
for i in range(1, n + 1):
    for j in range(1, i + 1):
        print(j, end=" ")
    print()`,

while_loop: `n = 1
total = 0
while n <= 5:
    total += n
    print("n =", n, "total =", total)
    n += 1
print("Final:", total)`,

function: `def add(x, y):
    result = x + y
    return result

def square(n):
    return n * n

a = 3
b = 7
print(add(a, b))
print(square(a))`,

recursion: `def factorial(n):
    if n <= 1:
        return 1
    return n * factorial(n - 1)

print(factorial(5))`,

r_fibo: `def fib(n):
    if n == 0:
        return 0
    if n == 1:
        return 1
    return fib(n - 1) + fib(n - 2)

for i in range(7):
    print("fib(" + str(i) + ") =", fib(i))`,

gcd: `def gcd(a, b):
    print("gcd(" + str(a) + ", " + str(b) + ")")
    if b == 0:
        return a
    return gcd(b, a % b)

print("GCD:", gcd(48, 18))`,

list_basics: `nums = [10, 20, 30, 40, 50]
total = 0
for n in nums:
    total += n
print("List:", nums)
print("Sum:", total)
nums.append(60)
print("After append:", nums)
print("nums[0] =", nums[0])
print("nums[-1] =", nums[-1])`,

list_slicing: `letters = ["a", "b", "c", "d", "e"]
print(letters[1:3])
print(letters[:2])
print(letters[-2:])
print(letters[::-1])`,

string_ops: `name = "Hello, World!"
print(name.upper())
print(name.lower())
print(len(name))
words = "the quick brown fox".split()
print(words)
print("-".join(words))
print(name.replace("World", "Python"))`,

aliasing: `a = [1, 2, 3]
b = a
b.append(4)
print("a:", a)
print("b:", b)
c = a.copy()
c.append(99)
print("a:", a)
print("c:", c)`,

dict_basics: `student = {"name": "Anisur", "age": 25, "gpa": 3.9}
print(student["name"])
student["major"] = "CS"
for key in student:
    print(key, "->", student[key])
print(student.get("minor", "none"))`,

word_count: `text = "the quick brown fox jumps over the lazy dog the fox runs"
words = text.split()
counts = {}
for w in words:
    if w in counts:
        counts[w] += 1
    else:
        counts[w] = 1
for w in counts:
    print(w, ":", counts[w])`,

class_like_dict: `def make_point(x, y):
    return {"x": x, "y": y}

def move(p, dx, dy):
    p["x"] += dx
    p["y"] += dy

p1 = make_point(3, 4)
print(p1)
move(p1, 1, -1)
print(p1)`,

linear_search: `def linear_search(arr, key):
    for i in range(len(arr)):
        if arr[i] == key:
            return i
    return -1

nums = [5, 3, 8, 1, 9, 2, 7]
result = linear_search(nums, 9)
print("Found at index:", result)`,

binary_search: `arr = [2, 5, 8, 12, 16, 23]
target = 12
low, high = 0, len(arr) - 1
found = -1
while low <= high:
    mid = (low + high) // 2
    print("Checking mid =", mid, "arr[mid] =", arr[mid])
    if arr[mid] == target:
        found = mid
        break
    elif arr[mid] < target:
        low = mid + 1
    else:
        high = mid - 1
print("Found at index:", found)`,

bubble_sort: `arr = [64, 34, 25, 12, 22]
n = len(arr)
for i in range(n - 1):
    for j in range(n - i - 1):
        if arr[j] > arr[j + 1]:
            temp = arr[j]
            arr[j] = arr[j + 1]
            arr[j + 1] = temp
print("Sorted:", arr)`,

selection_sort: `arr = [64, 25, 12, 22, 11]
n = len(arr)
for i in range(n - 1):
    min_idx = i
    for j in range(i + 1, n):
        if arr[j] < arr[min_idx]:
            min_idx = j
    arr[i], arr[min_idx] = arr[min_idx], arr[i]
    print("Pass", i + 1, ":", arr)
print("Sorted:", arr)`,

fibonacci: `a, b = 0, 1
for i in range(10):
    print(a)
    a, b = b, a + b`,

prime_check: `def is_prime(n):
    if n < 2:
        return False
    for i in range(2, n):
        if n % i == 0:
            return False
    return True

for n in range(2, 20):
    if is_prime(n):
        print(n, "is prime")`,
};

/* =========================================================================
   UI
   ========================================================================= */
let interp = null, curStep = -1, playTimer = null, stdinQ = [], execLine = null;

const root = document.documentElement;
const themeIcon = document.getElementById('theme-icon');
let currentTheme = 'light';
function applyTheme(t) {
  currentTheme = t;
  root.setAttribute('data-theme', t);
  themeIcon.className = t === 'dark' ? 'fa-solid fa-sun' : 'fa-solid fa-moon';
  cmEditor.setOption('theme', t === 'dark' ? 'one-dark' : 'default');
  setTimeout(() => cmEditor.refresh(), 50);
}
document.getElementById('theme-toggle').addEventListener('click', () => applyTheme(currentTheme === 'dark' ? 'light' : 'dark'));

const _isTouchDevice = ('ontouchstart' in window) || navigator.maxTouchPoints > 0 || /Android|iPhone|iPad|iPod/i.test(navigator.userAgent);

const cmEditor = CodeMirror.fromTextArea(document.getElementById('code-input'), {
  mode: 'python',
  theme: 'default',
  lineNumbers: true,
  matchBrackets: true,
  styleActiveLine: true,
  indentUnit: 4,
  tabSize: 4,
  indentWithTabs: false,
  extraKeys: { 'F5': () => runVisualize(), 'Ctrl-Enter': () => runVisualize(), 'Cmd-Enter': () => runVisualize() },
  lineWrapping: false,
  // Stick with the default 'textarea' input style even on mobile.
  // CodeMirror 5's 'contenteditable' mode is unreliable on Android/iOS
  // (composition/autocorrect bugs) and can block typing entirely.
});
cmEditor.setValue(SAMPLES.hello);
cmEditor.setSize('100%', '100%');

if (_isTouchDevice) {
  // On mobile, a tap sometimes lands on the CodeMirror wrapper without
  // properly focusing the underlying hidden <textarea>, so the OS never
  // raises the keyboard. A plain focus() call on tap, with no other side
  // effects, is enough to fix that without disturbing CodeMirror's own
  // touch/cursor handling.
  const cmWrapperEl = cmEditor.getWrapperElement();
  cmWrapperEl.addEventListener('touchend', function (e) {
    if (e.target.closest('.CodeMirror-scrollbar-filler, .CodeMirror-vscrollbar, .CodeMirror-hscrollbar')) return;
    if (!cmEditor.hasFocus()) cmEditor.focus();
  }, { passive: true });
}

const sampleSel = document.getElementById('sample-sel');
sampleSel.addEventListener('change', () => {
  const k = sampleSel.value;
  if (k && SAMPLES[k]) { cmEditor.setValue(SAMPLES[k]); resetViz(); }
  sampleSel.value = '';
});

document.getElementById('clear-btn').addEventListener('click', () => {
  cmEditor.setValue('# write your Python code here\n\n');
  cmEditor.setCursor(2, 0);
  cmEditor.focus();
  resetViz();
});

// resizable split
const resizeHandle = document.getElementById('resize-handle');
const editorPanel = document.getElementById('editor-panel');
let isResizing = false;
resizeHandle.addEventListener('mousedown', () => { isResizing = true; resizeHandle.classList.add('dragging'); document.body.style.cursor = 'col-resize'; document.body.style.userSelect = 'none'; });
document.addEventListener('mousemove', e => {
  if (!isResizing) return;
  const appRect = document.getElementById('app').getBoundingClientRect();
  let pct = ((e.clientX - appRect.left) / appRect.width) * 100;
  pct = Math.max(20, Math.min(80, pct));
  editorPanel.style.width = pct + '%';
  cmEditor.refresh();
});
document.addEventListener('mouseup', () => {
  if (isResizing) { isResizing = false; resizeHandle.classList.remove('dragging'); document.body.style.cursor = ''; document.body.style.userSelect = ''; cmEditor.refresh(); }
});

const runBtn = document.getElementById('run-btn'), resetBtn = document.getElementById('reset-btn');
const prevBtn = document.getElementById('prev-btn'), nextBtn = document.getElementById('next-btn');
const playBtn = document.getElementById('play-btn'), pauseBtn = document.getElementById('pause-btn');
const stepInfo = document.getElementById('step-info'), speedSlider = document.getElementById('speed');
const framesEl = document.getElementById('frames-pane');
const heapBlocksEl = document.getElementById('heap-blocks');
const outputArea = document.getElementById('output-area');
const stdinIn = document.getElementById('stdin-in'), stdinBtn = document.getElementById('stdin-btn');
const csEl = document.getElementById('cs-pane');
const mmEl = document.getElementById('mm-pane');
const walkEl = document.getElementById('walkthrough');
const sbDot = document.getElementById('sb-dot'), sbTxt = document.getElementById('sb-txt');
const sbLine = document.getElementById('sb-line'), sbStep = document.getElementById('sb-step'), sbFrames = document.getElementById('sb-frames');

stdinBtn.addEventListener('click', sendStdin);
stdinIn.addEventListener('keydown', e => { if (e.key === 'Enter') sendStdin(); });
function sendStdin() {
  const v = stdinIn.value.trim(); if (!v) return;
  stdinQ.push(v); stdinIn.value = '';
  outputArea.textContent += `[input queued: ${v}]\n`;
}

runBtn.addEventListener('click', runVisualize);
resetBtn.addEventListener('click', resetViz);

function runVisualize() {
  stopPlay();
  const code = cmEditor.getValue();
  if (!code.trim()) { showWalk('err', '<i class="fa-solid fa-triangle-exclamation"></i> Please enter some Python code.'); return; }
  setStatus('running', 'Interpreting…');
  clearOutput();
  try {
    interp = new PyInterpreter(code, stdinQ.slice());
    if (interp.errors.length) {
      showWalk('err', '<i class="fa-solid fa-triangle-exclamation"></i> ' + interp.errors.join('<br>'));
      setStatus('error', 'Error'); updateCtrl(); return;
    }
    if (!interp.steps.length) { showWalk('err', 'No steps generated.'); setStatus('error', 'No steps'); return; }
    curStep = 0; renderStep(0); updateCtrl();
    setStatus('ok', `Ready — ${interp.steps.length} steps`);
  } catch (e) {
    showWalk('err', '<i class="fa-solid fa-triangle-exclamation"></i> ' + (e.message || String(e)));
    setStatus('error', 'Error');
  }
}

function resetViz() {
  stopPlay(); interp = null; curStep = -1; stdinQ = [];
  clearOutput();
  framesEl.innerHTML = '<div class="frame-empty">No stack frames yet. Run the visualizer to see variables.</div>';
  heapBlocksEl.innerHTML = '<div class="empty"><i class="fa-solid fa-diagram-project"></i><p>No heap objects yet. Lists, dicts, and sets you create will appear here.</p></div>';
  csEl.innerHTML = '<div class="empty"><i class="fa-solid fa-layer-group"></i><p>No active function calls.</p></div>';
  mmEl.innerHTML = '<div class="empty"><i class="fa-solid fa-map"></i><p>No heap addresses allocated yet.</p></div>';
  showWalk('', '<b>Welcome to Python Visualizer Plus.</b><br>Write Python in the editor — or pick an example — then click <b>Visualize</b> to step through execution line by line.');
  clearLineHL(); updateCtrl(); setStatus('', 'Ready');
  sbLine.textContent = '—'; sbStep.textContent = '—'; sbFrames.textContent = '0';
}

function clearOutput() { outputArea.textContent = '— no output yet —'; }

prevBtn.addEventListener('click', stepPrev);
nextBtn.addEventListener('click', stepNext);
playBtn.addEventListener('click', startPlay);
pauseBtn.addEventListener('click', pausePlay);

function stepNext() { if (!interp || curStep >= interp.steps.length - 1) return; curStep++; renderStep(curStep); updateCtrl(); }
function stepPrev() { if (!interp || curStep <= 0) return; curStep--; renderStep(curStep); updateCtrl(); }
function startPlay() { if (!interp || curStep >= interp.steps.length - 1) return; playBtn.style.display = 'none'; pauseBtn.style.display = ''; schedulePlay(); }
function schedulePlay() {
  const delay = Math.max(60, 1150 - speedSlider.value * 110);
  playTimer = setTimeout(() => {
    if (curStep < interp.steps.length - 1) { curStep++; renderStep(curStep); updateCtrl(); schedulePlay(); }
    else pausePlay();
  }, delay);
}
function pausePlay() { clearTimeout(playTimer); playTimer = null; playBtn.style.display = ''; pauseBtn.style.display = 'none'; }
function stopPlay() { clearTimeout(playTimer); playTimer = null; playBtn.style.display = ''; pauseBtn.style.display = 'none'; }

function updateCtrl() {
  const has = !!interp && interp.steps && interp.steps.length > 0 && !interp.errors.length;
  prevBtn.disabled = !has || curStep <= 0;
  nextBtn.disabled = !has || curStep >= (interp?.steps.length || 1) - 1;
  playBtn.disabled = !has || curStep >= (interp?.steps.length || 1) - 1;
  const txt = has ? `Step ${curStep + 1} / ${interp.steps.length}` : 'Not running';
  stepInfo.textContent = txt;
  sbStep.textContent = has ? `${curStep + 1}/${interp.steps.length}` : '—';
}

document.addEventListener('keydown', e => {
  if (document.activeElement === stdinIn) return;
  if (cmEditor.hasFocus()) { if (e.key === 'F5') { e.preventDefault(); runVisualize(); } return; }
  if (e.key === 'ArrowRight' || e.key === 'ArrowDown') { e.preventDefault(); stepNext(); }
  if (e.key === 'ArrowLeft' || e.key === 'ArrowUp') { e.preventDefault(); stepPrev(); }
  if (e.key === ' ') { e.preventDefault(); playTimer ? pausePlay() : startPlay(); }
  if (e.key === 'F5') { e.preventDefault(); runVisualize(); }
});

function renderStep(idx) {
  const step = interp.steps[idx]; if (!step) return;
  showWalk('', step.desc || '');
  highlightLine(step.ln);
  sbLine.textContent = step.ln || '—';
  outputArea.textContent = step.out && step.out.length ? step.out : '— no output yet —';
  renderFrames(step.frames, step.chg);
  renderHeap(step.heap, step.writeAddr, step.writeIdx);
  renderCS(step.cs);
  renderMM(step.heap);
}

function highlightLine(ln) {
  clearLineHL();
  if (!ln || ln < 1) return;
  execLine = ln;
  try {
    cmEditor.addLineClass(ln - 1, 'background', 'cm-exec-line');
    cmEditor.addLineClass(ln - 1, 'gutter', 'cm-exec-gutter');
    cmEditor.scrollIntoView({ line: ln - 1, ch: 0 }, 80);
  } catch (e) {}
}
function clearLineHL() {
  if (execLine !== null) {
    try { cmEditor.removeLineClass(execLine - 1, 'background', 'cm-exec-line'); cmEditor.removeLineClass(execLine - 1, 'gutter', 'cm-exec-gutter'); } catch (e) {}
    execLine = null;
  }
}

function showWalk(type, html) { walkEl.className = 'wt-box' + (type ? ' ' + type : ''); walkEl.innerHTML = html; }

function fmtCell(v, heap) {
  if (v === null || v === undefined) return 'None';
  if (v === true) return 'True';
  if (v === false) return 'False';
  if (typeof v === 'string' && heap && heap[v]) return heapReprFromSnap(v, heap, new Set());
  if (typeof v === 'string') return `"${v.replace(/</g, '&lt;')}"`;
  if (typeof v === 'number') return String(v);
  if (v && v.__tuple) return '(' + v.items.map(x => fmtCell(x, heap)).join(', ') + (v.items.length === 1 ? ',' : '') + ')';
  if (v && v.__range) return `range(${v.start}, ${v.stop}${v.step !== 1 ? ', ' + v.step : ''})`;
  return String(v);
}
function heapReprFromSnap(addr, heap, seen) {
  if (seen.has(addr)) return '[...]';
  seen.add(addr);
  const o = heap[addr]; if (!o) return 'None';
  if (o.kind === 'list' || o.kind === 'set') {
    const inner = o.items.map(x => (typeof x === 'string' && heap[x]) ? heapReprFromSnap(x, heap, seen) : fmtCell(x, heap)).join(', ');
    return o.kind === 'set' ? `{${inner}}` : `[${inner}]`;
  }
  if (o.kind === 'dict') {
    const inner = o.items.map(([k, v]) => `${fmtCell(k, heap)}: ${(typeof v === 'string' && heap[v]) ? heapReprFromSnap(v, heap, seen) : fmtCell(v, heap)}`).join(', ');
    return `{${inner}}`;
  }
  return 'None';
}
function pyType(v, heap) {
  if (v === null || v === undefined) return 'NoneType';
  if (typeof v === 'boolean') return 'bool';
  if (typeof v === 'number') return Number.isInteger(v) ? 'int' : 'float';
  if (typeof v === 'string' && heap && heap[v]) return heap[v].kind;
  if (typeof v === 'string') return 'str';
  if (v && v.__tuple) return 'tuple';
  if (v && v.__range) return 'range';
  return 'object';
}

function renderFrames(frames, chg) {
  if (!frames || !frames.length) {
    framesEl.innerHTML = '<div class="frame-empty">No stack frames yet. Run the visualizer to see variables.</div>';
    sbFrames.textContent = '0'; return;
  }
  sbFrames.textContent = frames.length;
  framesEl.innerHTML = '';
  for (let fi = frames.length - 1; fi >= 0; fi--) {
    const fr = frames[fi];
    const isActive = fi === frames.length - 1;
    const card = document.createElement('div');
    card.className = 'frame-card' + (isActive ? ' frame-active' : '');
    const hdr = document.createElement('div');
    hdr.className = 'frame-hdr';
    hdr.innerHTML = `<i class="fa-solid fa-cube" style="color:var(--ptr-color);font-size:11px"></i><span class="frame-fn">${fr.name}${fr.name === '[Global]' ? '' : '()'}</span>`;
    if (isActive) hdr.innerHTML += `<span class="frame-tag">Active</span>`;
    card.appendChild(hdr);

    const entries = Object.entries(fr.vars || {});
    if (!entries.length) {
      const em = document.createElement('div');
      em.className = 'frame-empty';
      em.textContent = 'No variables'; card.appendChild(em);
    } else {
      const wrap = document.createElement('div'); wrap.className = 'vtbl-wrap';
      const tbl = document.createElement('table');
      tbl.className = 'vtbl';
      tbl.innerHTML = `<thead><tr><th>Name</th><th>Type</th><th>Value</th></tr></thead>`;
      const tb = document.createElement('tbody');
      for (const [name, v] of entries) {
        const tr = document.createElement('tr');
        const isChanged = chg === name && isActive;
        if (isChanged) tr.classList.add('v-changed');
        const val = v.value;
        const isRef = typeof val === 'string' && interp && interp._heap && interp._heap[val];
        let vhtml;
        if (isRef) {
          vhtml = `<span class="vv vptr"><i class="fa-solid fa-arrow-right" style="font-size:10px"></i> ${val}</span>`;
        } else {
          const d = fmtCell(val, interp && interp._heap);
          vhtml = `<span class="vv${isChanged ? ' vc' : ''}">${String(d)}</span>`;
        }
        tr.innerHTML = `<td><span class="vn">${name}</span></td><td><span class="vt">${pyType(val, interp && interp._heap)}</span></td><td>${vhtml}</td>`;
        tb.appendChild(tr);
      }
      tbl.appendChild(tb);
      wrap.appendChild(tbl);
      card.appendChild(wrap);
    }
    framesEl.appendChild(card);
  }
}

function renderHeap(heap, writeAddr, writeIdx) {
  if (!heap || !Object.keys(heap).length) {
    heapBlocksEl.innerHTML = '<div class="empty"><i class="fa-solid fa-diagram-project"></i><p>No heap objects yet. Lists, dicts, and sets you create will appear here.</p></div>';
    return;
  }
  heapBlocksEl.innerHTML = '';
  for (const [addr, block] of Object.entries(heap)) {
    const d = document.createElement('div'); d.className = 'heap-block';
    const head = document.createElement('div'); head.className = 'hb-head';
    head.innerHTML = `<i class="fa-solid fa-cube" style="color:var(--ptr-color);font-size:11px"></i><span class="h-addr">${addr}</span><span class="h-sz">${block.items.length} item${block.items.length === 1 ? '' : 's'}</span><span class="h-kind">${block.kind}</span>`;
    d.appendChild(head);
    const body = document.createElement('div'); body.className = 'hb-body';
    if (block.kind === 'list' || block.kind === 'set') {
      const nums = block.items.filter(x => typeof x === 'number');
      const maxAbs = nums.length ? Math.max(...nums.map(x => Math.abs(x)), 1) : 1;
      const row = document.createElement('div'); row.className = 'arr-row';
      block.items.forEach((it, idx) => {
        const cell = document.createElement('div');
        const isWrite = addr === writeAddr && idx === writeIdx;
        cell.className = 'arr-cell' + (isWrite ? ' arr-cell-write' : '');
        let barHtml = '';
        if (typeof it === 'number') {
          const h = Math.max(4, Math.round((Math.abs(it) / maxAbs) * 46));
          barHtml = `<div class="ac-bar-track"><div class="ac-bar-fill" style="height:${h}px"></div></div>`;
        }
        cell.innerHTML = `<span class="ac-val">${fmtCell(it, heap)}</span>${barHtml}<span class="ac-idx">[${idx}]</span>`;
        row.appendChild(cell);
      });
      if (!block.items.length) row.innerHTML = '<span style="color:var(--text3);font-size:12px">(empty)</span>';
      body.appendChild(row);
    } else if (block.kind === 'dict') {
      const tbl = document.createElement('table'); tbl.className = 'dict-tbl';
      block.items.forEach(([k, v]) => {
        const tr = document.createElement('tr');
        tr.innerHTML = `<td>${fmtCell(k, heap)}</td><td>${fmtCell(v, heap)}</td>`;
        tbl.appendChild(tr);
      });
      if (!block.items.length) tbl.innerHTML = '<tr><td style="color:var(--text3)">(empty)</td></tr>';
      body.appendChild(tbl);
    }
    d.appendChild(body);
    heapBlocksEl.appendChild(d);
  }
}

function renderCS(stack) {
  csEl.innerHTML = '';
  if (!stack || !stack.length) {
    csEl.innerHTML = '<div class="empty"><i class="fa-solid fa-layer-group"></i><p>No active function calls. Code is running at module (global) scope.</p></div>';
    return;
  }
  for (let i = stack.length - 1; i >= 0; i--) {
    const d = document.createElement('div');
    d.className = 'cs-item' + (i === stack.length - 1 ? ' cs-top' : '');
    d.innerHTML = `<span class="cs-depth">#${stack.length - 1 - i}</span><i class="fa-solid fa-cube" style="color:var(--ptr-color);font-size:10px"></i><span class="cs-fn">${stack[i]}()</span><span class="cs-cur">${i === stack.length - 1 ? '← executing' : ''}</span>`;
    csEl.appendChild(d);
  }
}

function renderMM(heap) {
  if (!heap || !Object.keys(heap).length) {
    mmEl.innerHTML = '<div class="empty"><i class="fa-solid fa-map"></i><p>No heap addresses allocated yet.</p></div>';
    return;
  }
  const grid = document.createElement('div'); grid.className = 'mm-grid';
  for (const [addr, block] of Object.entries(heap)) {
    const cell = document.createElement('div'); cell.className = 'mm-cell mm-hp';
    cell.innerHTML = `<span class="mm-addr">${addr}</span><span class="mm-nm">${block.kind} · ${block.items.length} item${block.items.length === 1 ? '' : 's'}</span>`;
    grid.appendChild(cell);
  }
  mmEl.innerHTML = '';
  mmEl.appendChild(grid);
}

function setStatus(type, msg) {
  sbDot.style.color = type === 'ok' ? '#23d18b' : type === 'error' ? '#f48771' : 'var(--text3)';
  sbTxt.textContent = msg;
}

applyTheme('light');
resetViz();


(function () {
  const zoomInBtn = document.getElementById('zoom-in-btn');
  const zoomOutBtn = document.getElementById('zoom-out-btn');
  const zoomLabel = document.getElementById('zoom-level');
  const cmHost = document.getElementById('cm-host');
  if (!zoomInBtn || !zoomOutBtn || !cmHost) return;
  let zoom = 100;
  const MIN_ZOOM = 50, MAX_ZOOM = 500, STEP = 10;
  const BASE_FONT_SIZE = 14, BASE_LINE_HEIGHT = 21;
  function getCM() { const wrapper = cmHost.querySelector('.CodeMirror'); return wrapper && wrapper.CodeMirror ? wrapper.CodeMirror : null; }
  function applyEditorZoom() {
    const fontSize = BASE_FONT_SIZE * zoom / 100;
    const lineHeight = BASE_LINE_HEIGHT * zoom / 100;
    cmHost.style.setProperty('--code-font-size', fontSize + 'px');
    cmHost.style.setProperty('--code-line-height', lineHeight + 'px');
    const cm = getCM();
    if (cm) cm.refresh(); else window.dispatchEvent(new Event('resize'));
    zoomLabel.textContent = zoom + '%';
    zoomOutBtn.disabled = zoom <= MIN_ZOOM;
    zoomInBtn.disabled = zoom >= MAX_ZOOM;
  }
  function setZoom(value) { zoom = Math.max(MIN_ZOOM, Math.min(MAX_ZOOM, value)); applyEditorZoom(); }
  zoomInBtn.addEventListener('click', () => setZoom(zoom + STEP));
  zoomOutBtn.addEventListener('click', () => setZoom(zoom - STEP));
  document.addEventListener('keydown', function (e) {
    if (!(e.ctrlKey || e.metaKey)) return;
    if (e.key === '+' || e.key === '=') { e.preventDefault(); setZoom(zoom + STEP); }
    else if (e.key === '-') { e.preventDefault(); setZoom(zoom - STEP); }
    else if (e.key === '0') { e.preventDefault(); setZoom(100); }
  });
  let refreshTimer = null;
  function scheduleRefresh() { clearTimeout(refreshTimer); refreshTimer = setTimeout(() => { const cm = getCM(); if (cm) cm.refresh(); }, 120); }
  // IMPORTANT: do NOT observe { childList: true, subtree: true } on cmHost.
  // CodeMirror rewrites its own line DOM on every keystroke, so a subtree
  // observer fires constantly while typing, and each fire schedules a
  // cm.refresh(). On mobile, refresh() mid-composition resets CodeMirror's
  // internal render/selection state, which is exactly what makes a just
  // typed character flash and then disappear. We only need to react to
  // actual layout changes (e.g. this host resizing or its style/class
  // changing), never to the editor's own content mutations.
  const observer = new MutationObserver(scheduleRefresh);
  function start() {
    const cm = getCM();
    if (!cm) { setTimeout(start, 50); return; }
    observer.observe(cmHost, { attributes: true, attributeFilter: ['style', 'class'] });
    if (typeof ResizeObserver !== 'undefined') {
      const ro = new ResizeObserver(scheduleRefresh);
      ro.observe(cmHost);
    } else {
      window.addEventListener('resize', scheduleRefresh);
    }
    applyEditorZoom();
  }
  start();
})();
