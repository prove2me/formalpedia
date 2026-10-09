-- Prove2me | Theorems.Thm_EmpiricalDRO_Consistency_neg_log_one_sub_le
-- name    : EmpiricalDRO.Consistency.neg_log_one_sub_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-08T16:06:52.640018+00:00
-- url     : https://prove2.me/theorems/a42f4339-c176-4ded-a962-f228c4cb7a88
-- title:
--   Proof of Theorem 6, p. 34 — −log(1 − t) ≤ t + 2t² for |t| ≤ 1/2
-- statement:
--   For every real $t$ with $|t|\le 1/2$,
--   $$
--   -\log(1-t)\le t+2t^2 .
--   $$
--
--   In the proof of Theorem 6 (and hence of Theorem 3) this inequality, applied with $t=\tilde h(x;\xi_i)/\lambda_n$, turns the dual objective (76) into the explicit upper bound (77).
-- source:
--   Lam, Recovering Best Statistical Guarantees via the Empirical DRO, arXiv:1605.09349v1, p. 34, proof of Theorem 6, the sentence before (77)

import Mathlib
import Definitions.Def_EmpiricalDRO_Consistency_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace EmpiricalDRO.Consistency

/-- The elementary inequality used in the proof of Theorem 6, Lam, arXiv:1605.09349v1, p. 34:
`−log(1 − t) ≤ t + 2t²` for every `|t| ≤ 1/2`. -/
theorem neg_log_one_sub_le : ∀ t : ℝ, |t| ≤ 1 / 2 → -Real.log (1 - t) ≤ t + 2 * t ^ 2 := by sorry

end EmpiricalDRO.Consistency
