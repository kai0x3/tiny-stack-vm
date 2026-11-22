// A tiny stack virtual machine for make.fun's tiny stack ISA (the kit's
// generator/subject/ISA.md). Each step checks, in the ISA's order: step limit,
// pc in range, opcode, immediate fits, stack under/overflow, the trap, the effect.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

/** Runs program p on input inp. */
function run(p: Uint8Array, inp: Uint8Array): [Uint8Array, number] {
  const n = p.length;
  const D = new Int32Array(256); // data stack, at most 256 values
  const C = new Int32Array(64); // call stack, at most 64 return addresses
  const M = new Int32Array(256); // memory words 0..255
  const out = new Uint8Array(65536);
  let sp = 0, csp = 0, olen = 0, ip = 0, pc = 0, steps = 0;
  const end = (code: number): [Uint8Array, number] => [out.slice(0, olen), code];
  for (;;) {
    if (steps === 1000000) return end(10); // step limit
    if (pc < 0 || pc >= n) return end(9);
    const op = p[pc];
    steps++;
    switch (op) {
      case 0x00: return end(0);
      case 0x01: { // PUSH8: the byte as a signed 8-bit number
        if (pc + 1 >= n) return end(9);
        if (sp === 256) return end(3);
        D[sp++] = (p[pc + 1] << 24) >> 24;
        pc += 2;
        break;
      }
      case 0x02: { // PUSH32: four bytes, little-endian, signed
        if (pc + 4 >= n) return end(9);
        if (sp === 256) return end(3);
        D[sp++] = p[pc + 1] | (p[pc + 2] << 8) | (p[pc + 3] << 16) | (p[pc + 4] << 24);
        pc += 5;
        break;
      }
      case 0x03: // POP
        if (sp < 1) return end(2);
        sp--; pc++; break;
      case 0x04: // DUP
        if (sp < 1) return end(2);
        if (sp === 256) return end(3);
        D[sp] = D[sp - 1]; sp++; pc++; break;
      case 0x05: { // SWAP
        if (sp < 2) return end(2);
        const t = D[sp - 1];
        D[sp - 1] = D[sp - 2];
        D[sp - 2] = t;
        pc++;
        break;
      }
      case 0x06: // OVER
        if (sp < 2) return end(2);
        if (sp === 256) return end(3);
        D[sp] = D[sp - 2]; sp++; pc++; break;
      case 0x07: { // ROT: ( a b c -- b c a )
        if (sp < 3) return end(2);
        const a = D[sp - 3];
        D[sp - 3] = D[sp - 2];
        D[sp - 2] = D[sp - 1];
        D[sp - 1] = a;
        pc++;
        break;
      }
      case 0x17: // NEG: wraps, -(-2^31) is -2^31
        if (sp < 1) return end(2);
        D[sp - 1] = -D[sp - 1] | 0; pc++; break;
      case 0x1b: // NOT
        if (sp < 1) return end(2);
        D[sp - 1] = ~D[sp - 1]; pc++; break;
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
      case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e:
      case 0x20: case 0x21: case 0x22: {
        // Binary operators: pop b (the top), then a, push the result.
        if (sp < 2) return end(2);
        const b = D[sp - 1];
        const a = D[sp - 2];
        let r: number;
        switch (op) {
          case 0x10: r = (a + b) | 0; break;
          case 0x11: r = (a - b) | 0; break;
          case 0x12: r = Math.imul(a, b); break; // low 32 bits of the exact product
          case 0x13: // DIV: signed, truncated toward zero
            if (b === 0) return end(4);
            r = a === -2147483648 && b === -1 ? a : (a / b) | 0;
            break;
          case 0x14: // MOD: remainder takes the sign of a; x % -1 is 0
            if (b === 0) return end(4);
            r = b === -1 ? 0 : (a % b) | 0;
            break;
          case 0x15: // DIVU: a and b read as unsigned
            if (b === 0) return end(4);
            r = Math.floor((a >>> 0) / (b >>> 0)) | 0;
            break;
          case 0x16: // MODU
            if (b === 0) return end(4);
            r = ((a >>> 0) % (b >>> 0)) | 0;
            break;
          case 0x18: r = a & b; break;
          case 0x19: r = a | b; break;
          case 0x1a: r = a ^ b; break;
          case 0x1c: r = a << (b & 31); break; // only the low 5 bits of the count
          case 0x1d: r = a >> (b & 31); break; // arithmetic
          case 0x1e: r = (a >>> (b & 31)) | 0; break; // logical
          case 0x20: r = a === b ? 1 : 0; break;
          case 0x21: r = a < b ? 1 : 0; break;
          default: r = (a >>> 0) < (b >>> 0) ? 1 : 0; break; // LTU
        }
        D[sp - 2] = r;
        sp--;
        pc++;
        break;
      }
      case 0x30: case 0x31: case 0x32: { // JMP, JZ, JNZ: pc = next + signed offset
        if (pc + 2 >= n) return end(9);
        const rel = ((p[pc + 1] | (p[pc + 2] << 8)) << 16) >> 16;
        let take = true;
        if (op !== 0x30) {
          if (sp < 1) return end(2);
          const v = D[--sp];
          take = op === 0x31 ? v === 0 : v !== 0;
        }
        pc = take ? pc + 3 + rel : pc + 3;
        break;
      }
      case 0x33: { // CALL: push the next address, jump to the unsigned immediate
        if (pc + 2 >= n) return end(9);
        if (csp === 64) return end(7);
        C[csp++] = pc + 3;
        pc = p[pc + 1] | (p[pc + 2] << 8);
        break;
      }
      case 0x34: // RET
        if (csp === 0) return end(8);
        pc = C[--csp]; break;
      case 0x40: { // LOAD
        if (sp < 1) return end(2);
        const addr = D[sp - 1];
        if (addr < 0 || addr > 255) return end(6);
        D[sp - 1] = M[addr];
        pc++;
        break;
      }
      case 0x41: { // STORE: ( v addr -- )
        if (sp < 2) return end(2);
        const addr = D[sp - 1];
        if (addr < 0 || addr > 255) return end(6);
        M[addr] = D[sp - 2];
        sp -= 2;
        pc++;
        break;
      }
      case 0x50: { // PRINT: decimal ASCII, no padding, no newline
        if (sp < 1) return end(2);
        const s = String(D[sp - 1]);
        if (olen + s.length > 65536) return end(11); // writes none of its bytes
        for (let i = 0; i < s.length; i++) out[olen++] = s.charCodeAt(i);
        sp--;
        pc++;
        break;
      }
      case 0x51: // PUTC: one byte, v AND 255
        if (sp < 1) return end(2);
        if (olen + 1 > 65536) return end(11);
        out[olen++] = D[--sp] & 255; pc++; break;
      case 0x52: // IN: next input byte, -1 once the input is used up
        if (sp === 256) return end(3);
        D[sp++] = ip < inp.length ? inp[ip++] : -1; pc++; break;
      case 0x53: // EXIT: the code is v AND 255
        if (sp < 1) return end(2);
        return end(D[sp - 1] & 255);
      default: return end(5); // no opcode names the byte
    }
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  const [bytes, code] = run(readFileSync(join(I, id, 'program.bin')), readFileSync(join(I, id, 'input.bin')));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), bytes);
  writeFileSync(join(O, id, 'exit.txt'), code + '\n');
}
