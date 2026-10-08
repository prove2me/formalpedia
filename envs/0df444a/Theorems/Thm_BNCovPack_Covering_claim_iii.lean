-- Prove2me | Theorems.Thm_BNCovPack_Covering_claim_iii
-- name    : BNCovPack.Covering.claim_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T18:29:49.677679+00:00
-- url     : https://prove2.me/theorems/535ce136-b94e-4bec-b0f1-7bd32d30509b
-- title:
--   Theorem 4.1, claim (iii) — cumulative phase cost
-- statement:
--   Suppose the phased scheme is currently in phase $r$, whose bound is $\alpha_r>0$. Write $X_q=\sum_i c_i x_i^{(q)}$ for the final primal cost of each earlier phase $q$ and the present cost of the current phase. Then
--
--   $$
--   \sum_{q\le r} X_q<2\alpha_r.
--   $$
--
--   The actual output uses the coordinatewise maximum of the phase vectors, so its cost is at most this cumulative phase cost. The strict form agrees with the finite geometric sum starting from the positive first bound.
-- source:
--   Buchbinder, Naor, Online Primal-Dual Algorithms for Covering and Packing, Math. Oper. Res. (2009), DOI 10.1287/moor.1080.0363, p. 8, Theorem 4.1, proof, claim (iii); p. 9, proof of (3)

import Mathlib
import Definitions.Def_BNCovPack_Covering_Run

namespace BNCovPack.Covering

open OnlinePrimalDual.GeneralPacking

/-- Theorem 4.1, proof, claim (iii), p. 8. The sum of all phase primal
costs through the current phase is strictly less than twice its alpha. -/
theorem claim_iii {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    {m : ℕ} (inst : GeneralInstance I (Fin m)) (B : ℝ) (hB : 0 < B)
    (hm : 0 < m) (J : ℕ) (hJ : 1 ≤ J ∧ J ≤ m)
    (hpositive : ∀ k : Fin m, k.val < J → ∃ i : I, 0 < inst.a i k) (s : State I m)
    (hrun : Run inst B hm J s) :
    totalPhaseCost inst s < 2 * s.current.alpha := by sorry

end BNCovPack.Covering
