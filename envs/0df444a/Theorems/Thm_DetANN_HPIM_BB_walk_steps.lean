-- Prove2me | Theorems.Thm_DetANN_HPIM_BB_walk_steps
-- name    : DetANN.HPIM.BB.walk_steps
-- status  : Proved
-- author  : @milia
-- created : 2026-11-17T14:18:00.232192+00:00
-- url     : https://prove2.me/theorems/17bab460-7809-4c75-9195-b6c39b53ec04
-- title:
--   Straight-line segments of the balancing block: walk, sizes and counts
-- statement:
--   Thirteen straight-line facts about the program $\mathrm{bb}$ of definition `DetANN_HPIMBalProg`, covering the preorder walk, the size pass and the component count.
--
--   Every conjunct has the same shape. Let $Q$ be a program that contains $\mathrm{bb}(o)$ at offset $o$ (`Embeds Q (bb off) off`), and let $s$ be a non-halted state at the stated pc with the stated hypotheses (usually `Consts s A`). Then after the stated number $t$ of steps (exactly, or some $t\le$ a bound), the run of $Q$ from $s$:
--   - is at the stated pc and has not halted;
--   - has the stated values in the changed registers and cells;
--   - leaves every other pointer register, all real registers, the real memory and all other integer cells unchanged;
--   - has work $s.\mathrm{work}+t$, and its `cellsWritten` set lies in the listed cells.
--
--   Below, $\mathrm{fa}(A,f,k)=A-5+f-5k$ is field $f$ of record $k$ (definition `DetANN_HPIMBalProg`).
--
--   1. **Setup** $0\to15$ in 15 steps: `Consts` with $A=$ pointer 13, record count $0$, cur $=$ pointer 17, DFS top $-1$; nothing written.
--   2. **Visit a leaf** $15\to34$ in 11 steps, when $I[\mathrm{cur}]=0$: record $n_0$ gets kind 0 and address cur, and the count becomes $n_0+1$.
--   3. **Visit a cut** $15\to15$ in 19 steps, when $I[\mathrm{cur}]=1$: record $n_0$ gets kind 1, address cur and link $=$ old top; the top becomes $n_0$, and cur moves to the left child $I[\mathrm{cur}+2]$.
--   4. **Pop** $34\to15$ in 14 steps, when the top $k\ge0$: cur becomes the right child of record $k$, and the top becomes its link.
--   5. **Walk done** $34\to48$ in 1 step, when the top is $-1$.
--   6. **Size at a leaf** $49\to49$ in 14 steps (index $k+1\mapsto k$): size 1, mark 0.
--   7. **Size at a cut** $49\to49$ in 29 steps: $\mathrm{size}_k=1+a+b$ from the sizes $a$ of record $k+1$ and $b$ of record $k+1+a$; mark 0.
--   8. **Start the recursion** $78\to87$ in 9 steps: frame base and pointer $A-5N$, fuel $N+1$, $j=0$.
--   9. **Jump** $48\to49$ in 1 step.
--   10. **Call with fuel 0** $87\to218$ in 10 steps: writes the null leaf $(0,0)$ at the output top $u$, which becomes $u+2$.
--   11. **Call head** $87\to94$ in 7 steps, when the fuel is positive: sets up the backward count over the subtree of $j$.
--   12. **Count at a leaf** $94\to94$ in at most 16 steps ($k\ge j$): field 4 of record $k$ becomes $e=1-\mathrm{mark}_k$.
--   13. **Count at a cut** $94\to94$ in at most 33 steps: field 4 of record $k$ becomes $e+a+b$, the counts of record $k+1$ and of the record after its subtree.
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

theorem walk_steps :
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (s : State) (hpc : s.core.pc = off) (hh : s.halted = false),
      (run Q s detTape 15).core.pc = off + 15 ∧ (run Q s detTape 15).halted = false ∧ Consts (run Q s detTape 15) (s.core.ptrs 13) ∧ (run Q s detTape 15).core.ptrs 41 = ((0 : ℕ) : ℤ) ∧ (run Q s detTape 15).core.ptrs 42 = s.core.ptrs 17 ∧ (run Q s detTape 15).core.ptrs 43 = -1 ∧ (∀ x < 40, (run Q s detTape 15).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 15).core.regs = s.core.regs ∧ (run Q s detTape 15).core.mem = s.core.mem ∧ (run Q s detTape 15).integerMemory = s.integerMemory ∧ (run Q s detTape 15).work = s.work + 15 ∧ cellsWritten Q s 15 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A u : ℤ) (n0 : ℕ) (s : State) (hpc : s.core.pc = off + 15) (hh : s.halted = false) (hC : Consts s A) (h42 : s.core.ptrs 42 = u) (h41 : s.core.ptrs 41 = n0) (hu : A ≤ u) (hk : s.integerMemory u = 0),
      (run Q s detTape 11).core.pc = off + 34 ∧ (run Q s detTape 11).halted = false ∧ (run Q s detTape 11).core.ptrs 41 = ((n0 + 1 : ℕ) : ℤ) ∧ (run Q s detTape 11).integerMemory (fa A 0 n0) = 0 ∧ (run Q s detTape 11).integerMemory (fa A 1 n0) = u ∧ (∀ z, z ≠ fa A 0 n0 → z ≠ fa A 1 n0 → (run Q s detTape 11).integerMemory z = s.integerMemory z) ∧ (∀ x, x ≠ 41 → x ≠ 44 → x ≠ 45 → x ≠ 67 → x ≠ 68 → (run Q s detTape 11).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 11).core.regs = s.core.regs ∧ (run Q s detTape 11).core.mem = s.core.mem ∧ (run Q s detTape 11).work = s.work + 11 ∧ ∀ c ∈ cellsWritten Q s 11, c = (false, fa A 0 n0) ∨ c = (false, fa A 1 n0)) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A u tp : ℤ) (n0 : ℕ) (s : State) (hpc : s.core.pc = off + 15) (hh : s.halted = false) (hC : Consts s A) (h42 : s.core.ptrs 42 = u) (h41 : s.core.ptrs 41 = n0) (h43 : s.core.ptrs 43 = tp) (hu : A ≤ u) (hk : s.integerMemory u = 1),
      (run Q s detTape 19).core.pc = off + 15 ∧ (run Q s detTape 19).halted = false ∧ (run Q s detTape 19).core.ptrs 41 = ((n0 + 1 : ℕ) : ℤ) ∧ (run Q s detTape 19).core.ptrs 42 = s.integerMemory (u + 2) ∧ (run Q s detTape 19).core.ptrs 43 = n0 ∧ (run Q s detTape 19).integerMemory (fa A 0 n0) = 1 ∧ (run Q s detTape 19).integerMemory (fa A 1 n0) = u ∧ (run Q s detTape 19).integerMemory (fa A 4 n0) = tp ∧ (∀ z, z ≠ fa A 0 n0 → z ≠ fa A 1 n0 → z ≠ fa A 4 n0 → (run Q s detTape 19).integerMemory z = s.integerMemory z) ∧ (∀ x, x ≠ 41 → x ≠ 42 → x ≠ 43 → x ≠ 44 → x ≠ 45 → x ≠ 67 → x ≠ 68 → (run Q s detTape 19).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 19).core.regs = s.core.regs ∧ (run Q s detTape 19).core.mem = s.core.mem ∧ (run Q s detTape 19).work = s.work + 19 ∧ ∀ c ∈ cellsWritten Q s 19, c = (false, fa A 0 n0) ∨ c = (false, fa A 1 n0) ∨ c = (false, fa A 4 n0)) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A : ℤ) (k : ℕ) (s : State) (hpc : s.core.pc = off + 34) (hh : s.halted = false) (hC : Consts s A) (h43 : s.core.ptrs 43 = k),
      (run Q s detTape 14).core.pc = off + 15 ∧ (run Q s detTape 14).halted = false ∧ (run Q s detTape 14).core.ptrs 42 = s.integerMemory (s.integerMemory (fa A 1 k) + 3) ∧ (run Q s detTape 14).core.ptrs 43 = s.integerMemory (fa A 4 k) ∧ (∀ x, x ≠ 42 → x ≠ 43 → x ≠ 44 → x ≠ 67 → x ≠ 71 → (run Q s detTape 14).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 14).core.regs = s.core.regs ∧ (run Q s detTape 14).core.mem = s.core.mem ∧ (run Q s detTape 14).integerMemory = s.integerMemory ∧ (run Q s detTape 14).work = s.work + 14 ∧ cellsWritten Q s 14 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A : ℤ) (s : State) (hpc : s.core.pc = off + 34) (hh : s.halted = false) (hC : Consts s A) (h43 : s.core.ptrs 43 = -1),
      (run Q s detTape 1).core.pc = off + 48 ∧ (run Q s detTape 1).halted = false ∧ (run Q s detTape 1).core = { s.core with pc := off + 48 } ∧ (run Q s detTape 1).integerMemory = s.integerMemory ∧ (run Q s detTape 1).work = s.work + 1 ∧ cellsWritten Q s 1 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A : ℤ) (k : ℕ) (s : State) (hpc : s.core.pc = off + 49) (hh : s.halted = false) (hC : Consts s A) (h46 : s.core.ptrs 46 = ((k + 1 : ℕ) : ℤ)) (hk : s.integerMemory (fa A 0 k) = 0),
      (run Q s detTape 14).core.pc = off + 49 ∧ (run Q s detTape 14).halted = false ∧ (run Q s detTape 14).core.ptrs 46 = (k : ℤ) ∧ (run Q s detTape 14).integerMemory (fa A 2 k) = 1 ∧ (run Q s detTape 14).integerMemory (fa A 3 k) = 0 ∧ (∀ z, z ≠ fa A 2 k → z ≠ fa A 3 k → (run Q s detTape 14).integerMemory z = s.integerMemory z) ∧ (∀ x, x ≠ 44 → x ≠ 45 → x ≠ 46 → x ≠ 56 → x ≠ 57 → x ≠ 58 → x ≠ 67 → x ≠ 72 → (run Q s detTape 14).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 14).core.regs = s.core.regs ∧ (run Q s detTape 14).core.mem = s.core.mem ∧ (run Q s detTape 14).work = s.work + 14 ∧ ∀ c ∈ cellsWritten Q s 14, c = (false, fa A 2 k) ∨ c = (false, fa A 3 k)) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A a b : ℤ) (k : ℕ) (s : State) (hpc : s.core.pc = off + 49) (hh : s.halted = false) (hC : Consts s A) (h46 : s.core.ptrs 46 = ((k + 1 : ℕ) : ℤ)) (hk : s.integerMemory (fa A 0 k) = 1) (ha : s.integerMemory (fa A 2 (k + 1)) = a) (hb : s.integerMemory (A - 3 - 5 * ((k : ℤ) + 1 + a)) = b),
      (run Q s detTape 29).core.pc = off + 49 ∧ (run Q s detTape 29).halted = false ∧ (run Q s detTape 29).core.ptrs 46 = (k : ℤ) ∧ (run Q s detTape 29).integerMemory (fa A 2 k) = 1 + a + b ∧ (run Q s detTape 29).integerMemory (fa A 3 k) = 0 ∧ (∀ z, z ≠ fa A 2 k → z ≠ fa A 3 k → (run Q s detTape 29).integerMemory z = s.integerMemory z) ∧ (∀ x, x ≠ 44 → x ≠ 45 → x ≠ 46 → x ≠ 56 → x ≠ 57 → x ≠ 58 → x ≠ 67 → x ≠ 72 → (run Q s detTape 29).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 29).core.regs = s.core.regs ∧ (run Q s detTape 29).core.mem = s.core.mem ∧ (run Q s detTape 29).work = s.work + 29 ∧ ∀ c ∈ cellsWritten Q s 29, c = (false, fa A 2 k) ∨ c = (false, fa A 3 k)) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A : ℤ) (N : ℕ) (s : State) (hpc : s.core.pc = off + 78) (hh : s.halted = false) (hC : Consts s A) (h41 : s.core.ptrs 41 = N),
      (run Q s detTape 9).core.pc = off + 87 ∧ (run Q s detTape 9).halted = false ∧ (run Q s detTape 9).core.ptrs 48 = A - 5 * (N : ℤ) ∧ (run Q s detTape 9).core.ptrs 47 = A - 5 * (N : ℤ) ∧ (run Q s detTape 9).core.ptrs 49 = ((N + 1 : ℕ) : ℤ) ∧ (run Q s detTape 9).core.ptrs 50 = ((0 : ℕ) : ℤ) ∧ (run Q s detTape 9).core.ptrs 17 = s.core.ptrs 15 ∧ (∀ x, x ≠ 17 → x ≠ 47 → x ≠ 48 → x ≠ 49 → x ≠ 50 → x ≠ 67 → (run Q s detTape 9).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 9).core.regs = s.core.regs ∧ (run Q s detTape 9).core.mem = s.core.mem ∧ (run Q s detTape 9).integerMemory = s.integerMemory ∧ (run Q s detTape 9).work = s.work + 9 ∧ cellsWritten Q s 9 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (s : State) (hpc : s.core.pc = off + 48) (hh : s.halted = false),
      (run Q s detTape 1).core.pc = off + 49 ∧ (run Q s detTape 1).halted = false ∧ (run Q s detTape 1).core.ptrs 46 = s.core.ptrs 41 ∧ (∀ x, x ≠ 46 → (run Q s detTape 1).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 1).core.regs = s.core.regs ∧ (run Q s detTape 1).core.mem = s.core.mem ∧ (run Q s detTape 1).integerMemory = s.integerMemory ∧ (run Q s detTape 1).work = s.work + 1 ∧ cellsWritten Q s 1 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A u : ℤ) (s : State) (hpc : s.core.pc = off + 87) (hh : s.halted = false) (hC : Consts s A) (h49 : s.core.ptrs 49 = 0) (h15 : s.core.ptrs 15 = u),
      (run Q s detTape 10).core.pc = off + 218 ∧ (run Q s detTape 10).halted = false ∧ (run Q s detTape 10).core.ptrs 15 = u + 2 ∧ (run Q s detTape 10).integerMemory u = 0 ∧ (run Q s detTape 10).integerMemory (u + 1) = 0 ∧ (∀ z, z ≠ u → z ≠ u + 1 → (run Q s detTape 10).integerMemory z = s.integerMemory z) ∧ (∀ x, x ≠ 15 → x ≠ 44 → x ≠ 56 → (run Q s detTape 10).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 10).core.regs = s.core.regs ∧ (run Q s detTape 10).core.mem = s.core.mem ∧ (run Q s detTape 10).work = s.work + 10 ∧ ∀ c ∈ cellsWritten Q s 10, c = (false, u) ∨ c = (false, u + 1)) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A : ℤ) (j : ℕ) (s : State) (hpc : s.core.pc = off + 87) (hh : s.halted = false) (hC : Consts s A) (h49 : 1 ≤ s.core.ptrs 49) (h50 : s.core.ptrs 50 = j),
      (run Q s detTape 7).core.pc = off + 94 ∧ (run Q s detTape 7).halted = false ∧ (run Q s detTape 7).core.ptrs 51 = s.integerMemory (fa A 2 j) ∧ (run Q s detTape 7).core.ptrs 46 = j + s.integerMemory (fa A 2 j) ∧ (run Q s detTape 7).core.ptrs 67 = 5 * (j : ℤ) ∧ (∀ x, x ≠ 44 → x ≠ 46 → x ≠ 51 → x ≠ 67 → (run Q s detTape 7).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape 7).core.regs = s.core.regs ∧ (run Q s detTape 7).core.mem = s.core.mem ∧ (run Q s detTape 7).integerMemory = s.integerMemory ∧ (run Q s detTape 7).work = s.work + 7 ∧ cellsWritten Q s 7 = ∅) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A j e : ℤ) (k : ℕ) (s : State) (hpc : s.core.pc = off + 94) (hh : s.halted = false) (hC : Consts s A) (h46 : s.core.ptrs 46 = ((k + 1 : ℕ) : ℤ)) (h50 : s.core.ptrs 50 = j) (hjk : j ≤ k) (hm : (s.integerMemory (fa A 3 k) = 0 ∧ e = 1) ∨ (s.integerMemory (fa A 3 k) = 1 ∧ e = 0)) (hk : s.integerMemory (fa A 0 k) = 0),
      ∃ t, t ≤ 16 ∧ (run Q s detTape t).core.pc = off + 94 ∧ (run Q s detTape t).halted = false ∧ (run Q s detTape t).core.ptrs 46 = (k : ℤ) ∧ (run Q s detTape t).integerMemory (fa A 4 k) = e ∧ (∀ z, z ≠ fa A 4 k → (run Q s detTape t).integerMemory z = s.integerMemory z) ∧ (∀ x, x ≠ 44 → x ≠ 45 → x ≠ 46 → x ≠ 56 → x ≠ 57 → x ≠ 58 → x ≠ 72 → x ≠ 73 → (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape t).core.regs = s.core.regs ∧ (run Q s detTape t).core.mem = s.core.mem ∧ (run Q s detTape t).work = s.work + t ∧ ∀ c ∈ cellsWritten Q s t, c = (false, fa A 4 k)) ∧
    (∀ (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A j e a z b : ℤ) (k : ℕ) (s : State) (hpc : s.core.pc = off + 94) (hh : s.halted = false) (hC : Consts s A) (h46 : s.core.ptrs 46 = ((k + 1 : ℕ) : ℤ)) (h50 : s.core.ptrs 50 = j) (hjk : j ≤ k) (hm : (s.integerMemory (fa A 3 k) = 0 ∧ e = 1) ∨ (s.integerMemory (fa A 3 k) = 1 ∧ e = 0)) (hk : s.integerMemory (fa A 0 k) = 1) (ha : s.integerMemory (fa A 4 (k + 1)) = a) (hz : s.integerMemory (fa A 2 (k + 1)) = z) (hb : s.integerMemory (A - 1 - 5 * ((k : ℤ) + 1 + z)) = b),
      ∃ t, t ≤ 33 ∧ (run Q s detTape t).core.pc = off + 94 ∧ (run Q s detTape t).halted = false ∧ (run Q s detTape t).core.ptrs 46 = (k : ℤ) ∧ (run Q s detTape t).integerMemory (fa A 4 k) = e + a + b ∧ (∀ z, z ≠ fa A 4 k → (run Q s detTape t).integerMemory z = s.integerMemory z) ∧ (∀ x, x ≠ 44 → x ≠ 45 → x ≠ 46 → x ≠ 56 → x ≠ 57 → x ≠ 58 → x ≠ 72 → x ≠ 73 → (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧ (run Q s detTape t).core.regs = s.core.regs ∧ (run Q s detTape t).core.mem = s.core.mem ∧ (run Q s detTape t).work = s.work + t ∧ ∀ c ∈ cellsWritten Q s t, c = (false, fa A 4 k)) := by sorry

end DetANN.HPIM.BB
