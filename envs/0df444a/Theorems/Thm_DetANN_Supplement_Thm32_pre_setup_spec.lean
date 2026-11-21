-- Prove2me | Theorems.Thm_DetANN_Supplement_Thm32_pre_setup_spec
-- name    : DetANN.Supplement.Thm32.pre_setup_spec
-- status  : Proved
-- author  : @milia
-- created : 2026-11-21T03:40:26.511206+00:00
-- url     : https://prove2.me/theorems/0892bdd7-714a-4d8a-9668-4586c61655ed
-- title:
--   Setup and Hadamard columns of the construction program
-- statement:
--   Let $Q$ contain $\mathrm{pre}(q,o)$ (definition `DetANN_Supplement_PreProg`) at offset $o$. Let $s$ be a running state at $o$ with pointer 0 equal to $0$, integer cell 0 equal to $n$, integer cell 1 equal to $d=2^k$ and real cell 0 equal to $\tau$. Write $H_b=1+nd$.
--
--   Then for some $T\le 25+4n+6k+4\cdot2^k+2^k\big(k(10\cdot2^k+8)+5\cdot2^k+14\big)$ the run of $Q$ from $s$ is at $o+67$ after $T$ steps, has not halted, and:
--   - pointers $0,1,2,3,4,22,23,24$ hold $0,1,2,d,k,n,H_b+d^2,H_b$; pointers above 25 are unchanged;
--   - reals $5,6,7,8$ hold $\tau,0,1,-1$; reals above 8 are unchanged;
--   - integer cell $2+u$ holds $2^u$ ($u<k$); integer cells 0, 1 are unchanged;
--   - the Sylvester columns are stored: $\mathrm{mem}(H_b+rd+j)=\mathrm{sylvester}\,k\ j\ r$ for $r,j<d$;
--   - the real cells outside $[H_b,H_b+d^2)$ are unchanged, and the work grows by exactly $T$.
-- source:
--   Original, written for the mission 'Deterministic Approximate Nearest Neighbors in High Dimensions' as part of a proof of DetANN.Supplement.theorem_3_2 (Feng, Indyk, STOC 2027 submission, Theorem 3.2, p.7; the construction of §6.1, p.14, and Lemma 6.2). The machine is PNormReg (definition PNormReg_Machine) with the conventions of DetANN_DataStructure.

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_DetANN_DataStructure
import Definitions.Def_PNormRegLib_Reloc
import Definitions.Def_DetANN_Sylvester
import Definitions.Def_DetANN_SignedBlocks
import Definitions.Def_DetANN_Supplement_EvProg
import Definitions.Def_DetANN_Supplement_PreProg
import Definitions.Def_DetANN_Supplement_PreDedup

namespace DetANN.Supplement.Thm32

open PNormReg PNormRegLib DetANN

/-- **Setup and Hadamard columns of `pre`.** From the input layout (`n` and `d = 2^k` in the integer
cells `0`, `1`, `τ` in real cell `0`, pointer `0` zero), the program `pre q` of definition
`DetANN_Supplement_PreProg` reaches `off + 67`. There the strides `2^u` are in the integer cells `2 + u`,
`Hb = 1 + n·d` is in pointer `24`, `top = Hb + d²` in pointer `23`, and column `r` of the Sylvester
matrix is at `Hb + r·d`: `mem (Hb + r·d + j) = sylvester k j r`. Cells outside `[Hb, Hb + d²)` and the
listed registers are unchanged. -/
theorem pre_setup_spec :
    ∀ (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (n k : ℕ) (τ : ℝ)
    (s : State) (hpc : s.core.pc = off + 0) (hh : s.halted = false) (h0 : s.core.ptrs 0 = 0)
    (hn : s.integerMemory 0 = n) (hd : s.integerMemory 1 = ((2 ^ k : ℕ) : ℤ))
    (hτ : s.core.mem 0 = τ),
    ∃ t, t ≤ 25 + 4 * n + 6 * k + 4 * 2 ^ k + 2 ^ k * (k * (10 * 2 ^ k + 8) + 5 * 2 ^ k + 14) ∧
      (run Q s detTape t).core.pc = off + 67 ∧ (run Q s detTape t).halted = false ∧
      (run Q s detTape t).core.ptrs 0 = 0 ∧ (run Q s detTape t).core.ptrs 1 = 1 ∧
      (run Q s detTape t).core.ptrs 2 = 2 ∧ (run Q s detTape t).core.ptrs 3 = ((2 ^ k : ℕ) : ℤ) ∧
      (run Q s detTape t).core.ptrs 4 = k ∧ (run Q s detTape t).core.ptrs 22 = n ∧
      (run Q s detTape t).core.ptrs 23 = ((1 + n * 2 ^ k + 2 ^ k * 2 ^ k : ℕ) : ℤ) ∧
      (run Q s detTape t).core.ptrs 24 = ((1 + n * 2 ^ k : ℕ) : ℤ) ∧
      (∀ x, 25 < x → (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape t).core.regs 5 = τ ∧ (run Q s detTape t).core.regs 6 = 0 ∧
      (run Q s detTape t).core.regs 7 = 1 ∧ (run Q s detTape t).core.regs 8 = -1 ∧
      (∀ x, 8 < x → (run Q s detTape t).core.regs x = s.core.regs x) ∧
      (∀ u : ℕ, u < k → (run Q s detTape t).integerMemory (2 + (u : ℤ)) = 2 ^ u) ∧
      (∀ z, z < 2 → (run Q s detTape t).integerMemory z = s.integerMemory z) ∧
      (∀ r j : Fin (2 ^ k), (run Q s detTape t).core.mem
        (((1 + n * 2 ^ k : ℕ) : ℤ) + (((r : ℕ) * 2 ^ k + j : ℕ) : ℤ)) = sylvester k j r) ∧
      (∀ z, (z < ((1 + n * 2 ^ k : ℕ) : ℤ) ∨ ((1 + n * 2 ^ k + 2 ^ k * 2 ^ k : ℕ) : ℤ) ≤ z) →
        (run Q s detTape t).core.mem z = s.core.mem z) ∧
      (run Q s detTape t).work = s.work + t := by sorry

end DetANN.Supplement.Thm32
