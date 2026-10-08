-- Prove2me | Theorems.Thm_BNCovPack_Covering_claim_i
-- name    : BNCovPack.Covering.claim_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T18:29:28.093652+00:00
-- url     : https://prove2.me/theorems/d98c18e4-b7a6-4938-bfee-3e904be65e9d
-- title:
--   Theorem 4.1, claim (i) — dual value of a finished phase
-- statement:
--   Consider the phased online fractional covering scheme with $B>0$ on a finite instance with $n\ge1$ covering variables, positive costs, nonnegative coefficients, and at least one positive coefficient in each arrived constraint. Let $\alpha_r$ and $y_{kr}$ be the bound and dual variables of a finished phase $r$. Then
--
--   $$
--   \sum_k y_{kr}\ge\frac{B\alpha_r}{2\log(2n)}.
--   $$
--
--   This lower bound supplies the dual objective that pays for the phase in the competitiveness estimate.
--
--   **Formalization Note** The sum includes all indexed constraints; unreached variables remain zero. The logarithm is natural.
-- source:
--   Buchbinder, Naor, Online Primal-Dual Algorithms for Covering and Packing, Math. Oper. Res. (2009), DOI 10.1287/moor.1080.0363, p. 8, Theorem 4.1, proof, claim (i); p. 9, proof of (1), display (4)

import Mathlib
import Definitions.Def_BNCovPack_Covering_Run

namespace BNCovPack.Covering

open OnlinePrimalDual.GeneralPacking

/-- Theorem 4.1, proof, claim (i), p. 8. Every finished phase has earned
dual objective at least `B α(r)/(2 log(2n))`. -/
theorem claim_i {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    {m : ℕ} (inst : GeneralInstance I (Fin m)) (B : ℝ) (hB : 0 < B)
    (hm : 0 < m) (J : ℕ) (hJ : 1 ≤ J ∧ J ≤ m)
    (hpositive : ∀ k : Fin m, k.val < J → ∃ i : I, 0 < inst.a i k) (s : State I m)
    (hrun : Run inst B hm J s) :
    ∀ p ∈ s.finished,
      B * p.alpha / (2 * Real.log (2 * (Fintype.card I : ℝ))) ≤ ∑ k : Fin m, p.y k := by sorry

end BNCovPack.Covering
