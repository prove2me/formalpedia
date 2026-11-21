-- Prove2me | Theorems.Thm_DetANN_Supplement_Thm32_ev_block
-- name    : DetANN.Supplement.Thm32.ev_block
-- status  : Proved
-- author  : @milia
-- created : 2026-11-20T23:50:44.042471+00:00
-- url     : https://prove2.me/theorems/3a60d92b-b3e5-4916-8d98-c3af911a55a7
-- title:
--   The evaluation program computes the signed Hadamard blocks
-- statement:
--   Let $Q$ be a program that contains $\mathrm{ev}(o)$ of definition `DetANN_Supplement_EvProg` at offset $o$. Let $k\ge0$, $L\ge1$, $\xi:[L]\times[2^k]\to\{\text{true},\text{false}\}$ and $z\in\mathbb R^{2^k}$. Let $s$ be a running state at $o$ such that:
--
--   - pointer 0 holds $0$, integer cell 0 holds $L$ and integer cell 1 holds $2^k$;
--   - real cell $-2^k-1-(\ell\cdot2^k+r)$ holds $\mathrm{signOf}(\xi_{\ell r})\in\{\pm1\}$;
--   - real cell $-1-r$ holds $z_r$.
--
--   Then for some $t\le 82\cdot L\cdot 2^k\,(1+k)$, the run of $Q$ from $s$ has halted after $t$ steps, its work has grown by $t$, and for all $j<2^k$, $\ell<L$,
--
--   $$\mathrm{mem}(j\cdot L+\ell)=\big(\mathrm{signedBlocks}\,(\mathrm{sylvester}\,k)\,L\,\xi\ j\ z\big)_\ell=(L\,2^k)^{-1/2}\sum_{r<2^k}h_{jr}\,\mathrm{signOf}(\xi_{\ell r})\,z_r .$$
--
--   This is the evaluation clause of `DetANN.Supplement.IsBlockConstruction` for the blocks of Theorem 3.2, in the layout that `queryState` produces. Since $2^k\le n$, the bound $82L2^k(1+k)$ is $O(b\,d\,(1+\log n))$ with $b=L$.
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

/-- **The program `ev` evaluates the signed Hadamard blocks.** Let `Q` contain `ev off` (definition
`DetANN_Supplement_EvProg`) at offset `off`, and let `s` be a running state at `off` with pointer `0`
equal to `0`, `L ≥ 1` in integer cell `0`, `2^k` in integer cell `1`, the sign `signOf (ξ ℓ r)` in real
cell `-2^k - 1 - (ℓ·2^k + r)` and the query coordinate `z r` in real cell `-1 - r`. Then within
`82·L·2^k·(1 + k)` steps the run halts, and real cell `j·L + ℓ` holds
`signedBlocks (sylvester k) L ξ j z ℓ`, i.e. `(A_j z)_ℓ` for the blocks of §6.1. -/
theorem ev_block :
    ∀ (Q : Program) (off : ℕ) (hE : Embeds Q (ev off) off) (k L : ℕ) (hL : 1 ≤ L)
    (ξ : Fin L → Fin (2 ^ k) → Bool) (z : EuclideanSpace ℝ (Fin (2 ^ k))) (s : State)
    (hpc : s.core.pc = off) (hh : s.halted = false) (h0 : s.core.ptrs 0 = 0)
    (hLm : s.integerMemory 0 = L) (hd : s.integerMemory 1 = 2 ^ k)
    (hsg : ∀ (ℓ : Fin L) (r : Fin (2 ^ k)),
      s.core.mem (-(2 ^ k : ℤ) - 1 - ((ℓ : ℤ) * 2 ^ k + r)) = signOf (ξ ℓ r))
    (hz : ∀ r : Fin (2 ^ k), s.core.mem (-1 - (r : ℤ)) = z r),
    ∃ t, t ≤ 82 * (L * 2 ^ k * (1 + k)) ∧ (run Q s detTape t).halted = true ∧
      (run Q s detTape t).work = s.work + t ∧
      ∀ (j : Fin (2 ^ k)) (ℓ : Fin L),
        (run Q s detTape t).core.mem ((j : ℤ) * L + ℓ) = signedBlocks (sylvester k) L ξ j z ℓ := by sorry

end DetANN.Supplement.Thm32
