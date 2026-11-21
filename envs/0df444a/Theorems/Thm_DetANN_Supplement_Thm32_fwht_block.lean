-- Prove2me | Theorems.Thm_DetANN_Supplement_Thm32_fwht_block
-- name    : DetANN.Supplement.Thm32.fwht_block
-- status  : Proved
-- author  : @milia
-- created : 2026-11-20T23:50:36.692479+00:00
-- url     : https://prove2.me/theorems/010ad1ef-7247-4d54-96d0-cd95c5af52b3
-- title:
--   The FWHT block computes the Sylvester–Hadamard transform in place
-- statement:
--   Let $Q$ be a program that contains the FWHT block $\mathrm{fw}(o)$ of definition `DetANN_Supplement_EvProg` at offset $o$. Let $s$ be a running state at $o$ such that:
--
--   - pointer 3 holds $d=2^k$ and pointer 4 holds $k$; pointer 0 holds $0$ and pointer 2 holds $2$;
--   - integer cell $2+u$ holds $2^u$ for every $u<k$;
--   - the real cells $b,\dots,b+d-1$ hold $g(0),\dots,g(d-1)$, where $b$ is pointer 13.
--
--   Then for some $T\le k\,(10\cdot2^k+8)+2$, the run of $Q$ from $s$ is at $o+23$ after $T$ steps and has not halted, and
--
--   $$\mathrm{mem}(b+i)=\sum_{r<d}(-1)^{\langle i,r\rangle}\,g(r)=\big(\mathrm{sylvester}\,k\cdot g\big)_i\qquad(i<d).$$
--
--   Moreover:
--   - only pointers 5–12, reals 0–3 and the cells $b,\dots,b+d-1$ change, and these cells are the only ones written;
--   - the integer memory is unchanged, and the work grows by exactly $T$.
-- source:
--   Original, written for the mission 'Deterministic Approximate Nearest Neighbors in High Dimensions' as part of a proof of DetANN.Supplement.theorem_3_2 (Feng, Indyk, STOC 2027 submission, Theorem 3.2, p.7; the blocks of §6.1, p.14). The machine is PNormReg (definition PNormReg_Machine) with the conventions of DetANN_DataStructure; the fast Walsh–Hadamard transform is the standard in-place butterfly algorithm.

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_DetANN_DataStructure
import Definitions.Def_PNormRegLib_Reloc
import Definitions.Def_DetANN_Sylvester
import Definitions.Def_DetANN_SignedBlocks
import Definitions.Def_DetANN_Supplement_EvProg

namespace DetANN.Supplement.Thm32

open PNormReg PNormRegLib DetANN

/-- **The FWHT block computes the Sylvester–Hadamard transform in place.** Let `Q` contain the block
`fw off` (definition `DetANN_Supplement_EvProg`) at offset `off`, and let `s` be a running state at
`off` with `d = 2^k` in pointer `3`, `k` in pointer `4`, pointer `0` equal to `0`, pointer `2` equal to
`2`, the strides `2^u` (`u < k`) in the integer cells `2 + u`, and the reals `g 0, …, g (d-1)` at the
real cells `b, …, b + d - 1`, where `b` is pointer `13`. Then within `k (10·2^k + 8) + 2` steps the run
reaches `off + 23` without halting, the cells `b + i` hold `(sylvester k).mulVec g`, and only pointers
`5`–`12`, reals `0`–`3` and the cells `b, …, b + d - 1` change; these are also the only cells written. -/
theorem fwht_block :
    ∀ (Q : Program) (off : ℕ) (hE : Embeds Q (fw off) off) (k : ℕ) (b : ℤ)
    (g : ℕ → ℝ) (s : State) (hpc : s.core.pc = off + 0) (hh : s.halted = false)
    (h4 : s.core.ptrs 4 = k) (h0 : s.core.ptrs 0 = 0) (h2 : s.core.ptrs 2 = 2)
    (h3 : s.core.ptrs 3 = ((2 ^ k : ℕ) : ℤ)) (h13 : s.core.ptrs 13 = b)
    (hst : ∀ u : ℕ, u < k → s.integerMemory (2 + (u : ℤ)) = 2 ^ u)
    (hm : ∀ x : ℕ, x < 2 ^ k → s.core.mem (b + x) = g x),
    ∃ T, T ≤ k * (10 * 2 ^ k + 8) + 2 ∧ (run Q s detTape T).core.pc = off + 23 ∧
      (run Q s detTape T).halted = false ∧
      (∀ x, x ≠ 5 → x ≠ 6 → x ≠ 7 → x ≠ 8 → x ≠ 9 → x ≠ 10 → x ≠ 11 → x ≠ 12 →
        (run Q s detTape T).core.ptrs x = s.core.ptrs x) ∧
      (∀ x, x ≠ 0 → x ≠ 1 → x ≠ 2 → x ≠ 3 → (run Q s detTape T).core.regs x = s.core.regs x) ∧
      (∀ i : Fin (2 ^ k), (run Q s detTape T).core.mem (b + (i : ℕ)) =
        (sylvester k).mulVec (fun r => g r) i) ∧
      (∀ z, (z < b ∨ b + ((2 ^ k : ℕ) : ℤ) ≤ z) → (run Q s detTape T).core.mem z = s.core.mem z) ∧
      (run Q s detTape T).integerMemory = s.integerMemory ∧
      (run Q s detTape T).work = s.work + T ∧
      ∀ cc ∈ cellsWritten Q s T, cc.1 = true ∧ b ≤ cc.2 ∧ cc.2 < b + ((2 ^ k : ℕ) : ℤ) := by sorry

end DetANN.Supplement.Thm32
