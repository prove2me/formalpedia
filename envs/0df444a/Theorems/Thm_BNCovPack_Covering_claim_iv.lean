-- Prove2me | Theorems.Thm_BNCovPack_Covering_claim_iv
-- name    : BNCovPack.Covering.claim_iv
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T18:30:04.650231+00:00
-- url     : https://prove2.me/theorems/6f23509f-ba8f-43b5-919b-fd4b1882548b
-- title:
--   Theorem 4.1, claim (iv) — coverage of every arrived constraint
-- statement:
--   Let $x_i$ be the coordinatewise maximum of all completed phase vectors and the current phase vector after $J$ constraints have arrived and been processed by the phased online fractional covering scheme. For every arrived constraint $k<J$,
--
--   $$
--   \sum_i a_{ik}x_i\ge\frac1B.
--   $$
--
--   This is the scheme's online coverage guarantee, including constraints reprocessed after a phase restart. The coefficients are nonnegative and $B>0$.
-- source:
--   Buchbinder, Naor, Online Primal-Dual Algorithms for Covering and Packing, Math. Oper. Res. (2009), DOI 10.1287/moor.1080.0363, p. 8, Theorem 4.1, proof, claim (iv); p. 9, proof of (4)

import Mathlib
import Definitions.Def_BNCovPack_Covering_Run

namespace BNCovPack.Covering

open OnlinePrimalDual.GeneralPacking

/-- Theorem 4.1, proof, claim (iv), p. 8. The max-over-phases output
covers every constraint that has arrived, at level `1/B`. -/
theorem claim_iv {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    {m : ℕ} (inst : GeneralInstance I (Fin m)) (B : ℝ) (hB : 0 < B)
    (hm : 0 < m) (J : ℕ) (hJ : 1 ≤ J ∧ J ≤ m)
    (hpositive : ∀ k : Fin m, k.val < J → ∃ i : I, 0 < inst.a i k) (s : State I m)
    (hrun : Run inst B hm J s) :
    ∀ k : Fin m, k.val < J →
      1 / B ≤ ∑ i : I, inst.a i k * output s i := by sorry

end BNCovPack.Covering
