-- Prove2me | Theorems.Thm_DetANN_HPIM_BB_node_steps
-- name    : DetANN.HPIM.BB.node_steps
-- status  : Proved
-- author  : @milia
-- created : 2026-11-17T14:18:09.494632+00:00
-- url     : https://prove2.me/theorems/8fd81cb1-261f-425c-8cbe-67eb96da94ca
-- title:
--   Straight-line segments of the balancing block: scan, node, frames and marks
-- statement:
--   Twelve straight-line facts about the program $\mathrm{bb}$ of definition `DetANN_HPIMBalProg`, covering the leaf output, the centroid scan, the test node, the frame stack and the marking.
--
--   Every conjunct has the same shape. Let $Q$ be a program that contains $\mathrm{bb}(o)$ at offset $o$ (`Embeds Q (bb off) off`), and let $s$ be a non-halted state at the stated pc with the stated hypotheses (usually `Consts s A`). Then after the stated number $t$ of steps (exactly, or some $t\le$ a bound), the run of $Q$ from $s$:
--   - is at the stated pc and has not halted;
--   - has the stated values in the changed registers and cells;
--   - leaves every other pointer register, all real registers, the real memory and all other integer cells unchanged;
--   - has work $s.\mathrm{work}+t$, and its `cellsWritten` set lies in the listed cells.
--
--   Below, $\mathrm{fa}(A,f,k)=A-5+f-5k$ is field $f$ of record $k$ (definition `DetANN_HPIMBalProg`).
--
--   1. **Leaf output** $127\to218$ in at most 20 steps, when the total count is $\le1$: writes the leaf $(0,\mathrm{av})$ at $u$, where $\mathrm{av}$ is the stored answer of record $j$ (or 0 at a cut), and $u\mapsto u+2$.
--   2. **Scan start** $127\to135$ in 8 steps, when the total is $>1$.
--   3. **Scan exit** $135\to153$ in 2 steps, when the index reaches the end.
--   4. **Scan, marked** $135\to135$ in 9 steps: skips a marked record $k$.
--   5. **Scan, unmarked (load)** $135\to146$ in 10 steps: loads $c_k$ (field 4) into pointer 56.
--   6. **Scan, update** $146\to135$ in at most 7 steps: if $\max(c,\mathrm{tot}-c)$ is below the best score (pointer 54), it becomes the best score, and the best index (53) becomes the current one.
--   7. **Test node** $153\to176$ in 23 steps: writes kind 1, the box address $v$ and the yes-child address $u+4$ at $u,u+1,u+2$; sets the copy source to the stored box of the centroid $b$ and the copy length to $2m$.
--   8. **Copy step** $176\to176$ in 7 steps: copies one real cell of the box and advances the index.
--   9. **Push** $183\to87$ in 16 steps: pushes the frame $(j,b,u,\mathrm{fuel})$ below sp, decrements the fuel, advances the real heap by $2m$, and calls with $j=b$.
--   10. **Return** $218\to244$ in 26 steps, when $\mathrm{sp}<\mathrm{base}$: pops the frame, writes the no-child address at $u+3$, and sets up marking of the interval $[b,b+S_b)$.
--   11. **Mark step** $244\to244$ in 8 steps: sets the mark of record $i$ to 1.
--   12. **End** $218\to254$ in 1 step, when the stack is empty.
-- source:
--   Original, written for the mission 'Deterministic Approximate Nearest Neighbors in High Dimensions' as part of a floor-free proof of DetANN.lemma_3_3 (Feng, Indyk, STOC 2027 submission, Lemma 3.3, p.7). These are the straight-line pieces of the balancing block of DetANN.HPIM.balance_block, split out so that each proof fits the verifier's time limit. The machine is PNormReg (definition PNormReg_Machine) with the conventions of DetANN_DataStructure.

import Mathlib
import Definitions.Def_DetANN_HPIMBalProg
import Definitions.Def_PNormReg_Machine
import Definitions.Def_PNormRegLib_Exec
import Definitions.Def_DetANN_DataStructure
import Definitions.Def_PNormRegLib_Reloc

namespace DetANN.HPIM.BB

open PNormReg PNormRegLib DetANN DetANN.HPIM

theorem node_steps :
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A u tot av : ℤ) (j : ℕ) (s : State) (hpc : s.core.pc = off + 127) (hh : s.halted = false) (hC : Consts s A) (h67 : s.core.ptrs 67 = 5 * (j : ℤ)) (h15 : s.core.ptrs 15 = u) (htot : s.integerMemory (fa A 4 j) = tot) (htl : tot ≤ 1) (hu : A ≤ u) (hav : (s.integerMemory (fa A 0 j) = 0 ∧ s.integerMemory (s.integerMemory (fa A 1 j) + 2) = av) ∨ (s.integerMemory (fa A 0 j) = 1 ∧ av = 0)),
      ∃ t, t ≤ 20 ∧ (run Q s detTape t).core.pc = off + 218 ∧ (run Q s detTape t).halted = false ∧ (run Q s detTape t).core.ptrs 15 = u + 2 ∧ (run Q s detTape t).integerMemory u = 0 ∧ (run Q s detTape t).integerMemory (u + 1) = av ∧ (∀ z, z ≠ u → z ≠ u + 1 → (run Q s detTape t).integerMemory z = s.integerMemory z) ∧ (∀ x, x ≠ 15 → x ≠ 44 → x ≠ 45 → x ≠ 52 → x ≠ 56 → (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape t).core.regs = s.core.regs ∧ (run Q s detTape t).core.mem = s.core.mem ∧ (run Q s detTape t).work = s.work + t ∧ ∀ c ∈ cellsWritten Q s t, c = (false, u) ∨ c = (false, u + 1)) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A tot : ℤ) (j : ℕ) (s : State) (hpc : s.core.pc = off + 127) (hh : s.halted = false) (hC : Consts s A) (h67 : s.core.ptrs 67 = 5 * (j : ℤ)) (h50 : s.core.ptrs 50 = j) (htot : s.integerMemory (fa A 4 j) = tot) (htl : 2 ≤ tot),
      (run Q s detTape 8).core.pc = off + 135 ∧ (run Q s detTape 8).halted = false ∧ (run Q s detTape 8).core.ptrs 52 = tot ∧ (run Q s detTape 8).core.ptrs 54 = tot + 1 ∧ (run Q s detTape 8).core.ptrs 46 = j ∧ (run Q s detTape 8).core.ptrs 74 = j + s.core.ptrs 51 ∧ (∀ x, x ≠ 44 → x ≠ 46 → x ≠ 52 → x ≠ 54 → x ≠ 56 → x ≠ 74 → (run Q s detTape 8).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 8).core.regs = s.core.regs ∧ (run Q s detTape 8).core.mem = s.core.mem ∧ (run Q s detTape 8).integerMemory = s.integerMemory ∧ (run Q s detTape 8).work = s.work + 8 ∧ cellsWritten Q s 8 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A i e : ℤ) (s : State) (hpc : s.core.pc = off + 135) (hh : s.halted = false) (hC : Consts s A) (h46 : s.core.ptrs 46 = i) (h74 : s.core.ptrs 74 = e) (hie : e ≤ i + 1),
      (run Q s detTape 2).core.pc = off + 153 ∧ (run Q s detTape 2).halted = false ∧ (∀ x, x ≠ 46 → (run Q s detTape 2).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 2).core.regs = s.core.regs ∧ (run Q s detTape 2).core.mem = s.core.mem ∧ (run Q s detTape 2).integerMemory = s.integerMemory ∧ (run Q s detTape 2).work = s.work + 2 ∧ cellsWritten Q s 2 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A e : ℤ) (k : ℕ) (s : State) (hpc : s.core.pc = off + 135) (hh : s.halted = false) (hC : Consts s A) (h46 : s.core.ptrs 46 + 1 = k) (h74 : s.core.ptrs 74 = e) (hke : (k : ℤ) < e) (hm : s.integerMemory (fa A 3 k) = 1),
      (run Q s detTape 9).core.pc = off + 135 ∧ (run Q s detTape 9).halted = false ∧ (run Q s detTape 9).core.ptrs 46 = k ∧ (∀ x, x ≠ 44 → x ≠ 45 → x ≠ 46 → x ≠ 72 → (run Q s detTape 9).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 9).core.regs = s.core.regs ∧ (run Q s detTape 9).core.mem = s.core.mem ∧ (run Q s detTape 9).integerMemory = s.integerMemory ∧ (run Q s detTape 9).work = s.work + 9 ∧ cellsWritten Q s 9 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A e ci : ℤ) (k : ℕ) (s : State) (hpc : s.core.pc = off + 135) (hh : s.halted = false) (hC : Consts s A) (h46 : s.core.ptrs 46 + 1 = k) (h74 : s.core.ptrs 74 = e) (hke : (k : ℤ) < e) (hm : s.integerMemory (fa A 3 k) = 0) (hci : s.integerMemory (fa A 4 k) = ci),
      (run Q s detTape 10).core.pc = off + 146 ∧ (run Q s detTape 10).halted = false ∧ (run Q s detTape 10).core.ptrs 46 = k ∧ (run Q s detTape 10).core.ptrs 56 = ci ∧ (∀ x, x ≠ 44 → x ≠ 45 → x ≠ 46 → x ≠ 56 → x ≠ 72 → (run Q s detTape 10).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 10).core.regs = s.core.regs ∧ (run Q s detTape 10).core.mem = s.core.mem ∧ (run Q s detTape 10).integerMemory = s.integerMemory ∧ (run Q s detTape 10).work = s.work + 10 ∧ cellsWritten Q s 10 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (tot ci : ℤ) (s : State) (hpc : s.core.pc = off + 146) (hh : s.halted = false) (h52 : s.core.ptrs 52 = tot) (h56 : s.core.ptrs 56 = ci),
      ∃ t, t ≤ 7 ∧ (run Q s detTape t).core.pc = off + 135 ∧ (run Q s detTape t).halted = false ∧ (run Q s detTape t).core.ptrs 54 = (if max ci (tot - ci) < s.core.ptrs 54 then max ci (tot - ci) else s.core.ptrs 54) ∧ (run Q s detTape t).core.ptrs 53 = (if max ci (tot - ci) < s.core.ptrs 54 then s.core.ptrs 46 else s.core.ptrs 53) ∧ (∀ x, x ≠ 53 → x ≠ 54 → x ≠ 56 → x ≠ 57 → (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape t).core.regs = s.core.regs ∧ (run Q s detTape t).core.mem = s.core.mem ∧ (run Q s detTape t).integerMemory = s.integerMemory ∧ (run Q s detTape t).work = s.work + t ∧ cellsWritten Q s t = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A u v a src : ℤ) (b : ℕ) (s : State) (hpc : s.core.pc = off + 153) (hh : s.halted = false) (hC : Consts s A) (h15 : s.core.ptrs 15 = u) (h16 : s.core.ptrs 16 = v) (h53 : s.core.ptrs 53 = b) (hA : A ≤ 0) (hu : 0 ≤ u) (ha : s.integerMemory (fa A 1 b) = a) (ha1 : a + 1 < 0) (hs : s.integerMemory (a + 1) = src),
      (run Q s detTape 23).core.pc = off + 176 ∧ (run Q s detTape 23).halted = false ∧ (run Q s detTape 23).core.ptrs 55 = u ∧ (run Q s detTape 23).core.ptrs 15 = u + 4 ∧ (run Q s detTape 23).core.ptrs 44 = src ∧ (run Q s detTape 23).core.ptrs 57 = s.core.ptrs 1 + s.core.ptrs 1 ∧ (run Q s detTape 23).core.ptrs 46 = 0 ∧ (run Q s detTape 23).integerMemory u = 1 ∧ (run Q s detTape 23).integerMemory (u + 1) = v ∧ (run Q s detTape 23).integerMemory (u + 2) = u + 4 ∧ (∀ z, z ≠ u → z ≠ u + 1 → z ≠ u + 2 → (run Q s detTape 23).integerMemory z = s.integerMemory z) ∧ (∀ x, x ≠ 15 → x ≠ 44 → x ≠ 46 → x ≠ 55 → x ≠ 56 → x ≠ 57 → x ≠ 72 → (run Q s detTape 23).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 23).core.regs = s.core.regs ∧ (run Q s detTape 23).core.mem = s.core.mem ∧ (run Q s detTape 23).work = s.work + 23 ∧ ∀ c ∈ cellsWritten Q s 23, c = (false, u) ∨ c = (false, u + 1) ∨ c = (false, u + 2)) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (q : ℤ) (s : State) (hpc : s.core.pc = off + 176) (hh : s.halted = false) (h46 : s.core.ptrs 46 = q) (hq : q < s.core.ptrs 57),
      (run Q s detTape 7).core.pc = off + 176 ∧ (run Q s detTape 7).halted = false ∧ (run Q s detTape 7).core.ptrs 46 = q + 1 ∧ (∀ x, x ≠ 46 → x ≠ 58 → (run Q s detTape 7).core.ptrs x = s.core.ptrs x) ∧ (∀ x, x ≠ 40 → (run Q s detTape 7).core.regs x = s.core.regs x) ∧ (run Q s detTape 7).core.mem = Function.update s.core.mem (s.core.ptrs 16 + q) (s.core.mem (s.core.ptrs 44 + q)) ∧ (run Q s detTape 7).integerMemory = s.integerMemory ∧ (run Q s detTape 7).work = s.work + 7 ∧ ∀ c ∈ cellsWritten Q s 7, c = (true, s.core.ptrs 16 + q)) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (sp : ℤ) (s : State) (hpc : s.core.pc = off + 183) (hh : s.halted = false) (h47 : s.core.ptrs 47 = sp),
      (run Q s detTape 16).core.pc = off + 87 ∧ (run Q s detTape 16).halted = false ∧ (run Q s detTape 16).core.ptrs 16 = s.core.ptrs 16 + s.core.ptrs 57 ∧ (run Q s detTape 16).core.ptrs 47 = sp - 4 ∧ (run Q s detTape 16).core.ptrs 49 = s.core.ptrs 49 - 1 ∧ (run Q s detTape 16).core.ptrs 50 = s.core.ptrs 53 ∧ (run Q s detTape 16).integerMemory (sp - 4) = s.core.ptrs 50 ∧ (run Q s detTape 16).integerMemory (sp - 3) = s.core.ptrs 53 ∧ (run Q s detTape 16).integerMemory (sp - 2) = s.core.ptrs 55 ∧ (run Q s detTape 16).integerMemory (sp - 1) = s.core.ptrs 49 ∧ (∀ z, (z < sp - 4 ∨ sp ≤ z) → (run Q s detTape 16).integerMemory z = s.integerMemory z) ∧ (∀ x, x ≠ 16 → x ≠ 44 → x ≠ 47 → x ≠ 49 → x ≠ 50 → (run Q s detTape 16).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 16).core.regs = s.core.regs ∧ (run Q s detTape 16).core.mem = s.core.mem ∧ (run Q s detTape 16).work = s.work + 16 ∧ ∀ c ∈ cellsWritten Q s 16, c.1 = false ∧ sp - 4 ≤ c.2 ∧ c.2 < sp) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A sp base j b u f Sb : ℤ) (s : State) (hpc : s.core.pc = off + 218) (hh : s.halted = false) (hC : Consts s A) (h47 : s.core.ptrs 47 = sp) (h48 : s.core.ptrs 48 = base) (hsp : sp < base) (hsp0 : sp + 4 ≤ 0) (hu : 0 ≤ u) (hA : A ≤ 0) (f0 : s.integerMemory sp = j) (f1 : s.integerMemory (sp + 1) = b) (f2 : s.integerMemory (sp + 2) = u) (f3 : s.integerMemory (sp + 3) = f) (hb : 0 ≤ b) (hSb : s.integerMemory (A - 3 - 5 * b) = Sb),
      (run Q s detTape 26).core.pc = off + 244 ∧ (run Q s detTape 26).halted = false ∧ (run Q s detTape 26).core.ptrs 50 = j ∧ (run Q s detTape 26).core.ptrs 53 = b ∧ (run Q s detTape 26).core.ptrs 55 = u ∧ (run Q s detTape 26).core.ptrs 49 = f ∧ (run Q s detTape 26).core.ptrs 47 = sp + 4 ∧ (run Q s detTape 26).core.ptrs 74 = b + Sb ∧ (run Q s detTape 26).core.ptrs 46 = b ∧ (run Q s detTape 26).core.ptrs 56 = 1 ∧ (run Q s detTape 26).integerMemory (u + 3) = s.core.ptrs 15 ∧ (∀ z, z ≠ u + 3 → (run Q s detTape 26).integerMemory z = s.integerMemory z) ∧ (∀ x, x ≠ 44 → x ≠ 46 → x ≠ 47 → x ≠ 49 → x ≠ 50 → x ≠ 51 → x ≠ 53 → x ≠ 55 → x ≠ 56 → x ≠ 72 → x ≠ 74 → (run Q s detTape 26).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 26).core.regs = s.core.regs ∧ (run Q s detTape 26).core.mem = s.core.mem ∧ (run Q s detTape 26).work = s.work + 26 ∧ ∀ c ∈ cellsWritten Q s 26, c = (false, u + 3)) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A : ℤ) (i : ℕ) (s : State) (hpc : s.core.pc = off + 244) (hh : s.halted = false) (hC : Consts s A) (h46 : s.core.ptrs 46 = i) (h56 : s.core.ptrs 56 = 1) (hie : (i : ℤ) < s.core.ptrs 74),
      (run Q s detTape 8).core.pc = off + 244 ∧ (run Q s detTape 8).halted = false ∧ (run Q s detTape 8).core.ptrs 46 = ((i + 1 : ℕ) : ℤ) ∧ (run Q s detTape 8).integerMemory = Function.update s.integerMemory (fa A 3 i) 1 ∧ (∀ x, x ≠ 44 → x ≠ 46 → x ≠ 72 → (run Q s detTape 8).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 8).core.regs = s.core.regs ∧ (run Q s detTape 8).core.mem = s.core.mem ∧ (run Q s detTape 8).work = s.work + 8 ∧ ∀ c ∈ cellsWritten Q s 8, c = (false, fa A 3 i)) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (s : State) (hpc : s.core.pc = off + 218) (hh : s.halted = false) (hsp : s.core.ptrs 48 ≤ s.core.ptrs 47),
      (run Q s detTape 1).core.pc = off + 254 ∧ (run Q s detTape 1).halted = false ∧ (run Q s detTape 1).core = { s.core with pc := off + 254 } ∧ (run Q s detTape 1).integerMemory = s.integerMemory ∧ (run Q s detTape 1).work = s.work + 1 ∧ cellsWritten Q s 1 = ∅) := by sorry

end DetANN.HPIM.BB
