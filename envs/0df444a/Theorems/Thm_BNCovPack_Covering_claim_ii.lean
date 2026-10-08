-- Prove2me | Theorems.Thm_BNCovPack_Covering_claim_ii
-- name    : BNCovPack.Covering.claim_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T18:29:40.398133+00:00
-- url     : https://prove2.me/theorems/a9e8d807-045d-46fb-acbf-6f297b2eaf07
-- title:
--   Theorem 4.1, claim (ii) — phase dual feasibility
-- statement:
--   In every completed or current phase $r$ of the phased online fractional covering scheme, the phase's dual vector $y_{kr}$ is nonnegative and satisfies every dual packing constraint:
--
--   $$
--   \sum_k a_{ik}y_{kr}\le c_i\qquad(i\in I).
--   $$
--
--   Here $a_{ik}\ge0$ and $c_i>0$ are the instance coefficients and costs. Dual feasibility lets the phase dual objective serve as a lower bound on the cost of any unscaled covering solution.
--
--   **Formalization Note** A completed phase includes the partial last round that triggered its restart. Unreached dual coordinates are zero.
-- source:
--   Buchbinder, Naor, Online Primal-Dual Algorithms for Covering and Packing, Math. Oper. Res. (2009), DOI 10.1287/moor.1080.0363, p. 8, Theorem 4.1, proof, claim (ii); p. 9, proof of (2)

import Mathlib
import Definitions.Def_BNCovPack_Covering_Run

namespace BNCovPack.Covering

open OnlinePrimalDual.GeneralPacking

/-- Theorem 4.1, proof, claim (ii), p. 8. The dual vector of every phase,
including the current one, is feasible for the revealed packing constraints. -/
theorem claim_ii {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    {m : ℕ} (inst : GeneralInstance I (Fin m)) (B : ℝ) (hB : 0 < B)
    (hm : 0 < m) (J : ℕ) (hJ : 1 ≤ J ∧ J ≤ m)
    (hpositive : ∀ k : Fin m, k.val < J → ∃ i : I, 0 < inst.a i k) (s : State I m)
    (hrun : Run inst B hm J s) :
    ∀ p ∈ s.finished ++ [s.current],
      (∀ k : Fin m, 0 ≤ p.y k) ∧
      (∀ i : I, (∑ k : Fin m, inst.a i k * p.y k) ≤ inst.c i) := by sorry

end BNCovPack.Covering
