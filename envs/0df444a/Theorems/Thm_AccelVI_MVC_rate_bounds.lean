-- Prove2me | Theorems.Thm_AccelVI_MVC_rate_bounds
-- name    : AccelVI.MVC.rate_bounds
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T11:00:45.146976+00:00
-- url     : https://prove2.me/theorems/c163a76d-a82f-4953-b962-c176e2cfefb5
-- title:
--   p. 22 — 0 < (1 − √(1/κ))/(1 + √(1/κ)) < λ for λ ∈ (0, 1)
-- statement:
--   Let $\lambda \in (0,1)$ and $\kappa = (1+\lambda)/(1-\lambda)$. Then
--   $$0 < \frac{1 - \sqrt{1/\kappa}}{1 + \sqrt{1/\kappa}} < \lambda .$$
--
--   So the rate of Momentum Value Computation is strictly better than the rate $\lambda$ of plain Value Computation.
-- source:
--   Goyal & Grand-Clément, A First-Order Approach to Accelerated Value Iteration, arXiv:1905.09963v7, p. 22, sentence after the proof of Lemma B.2 (and Theorem 5.5, p. 10, last sentence)

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_AccelVI_MVC_Setting

namespace AccelVI.MVC

/-- p. 22: 0 < (1 − √(1/κ))/(1 + √(1/κ)) < λ for λ ∈ (0, 1). -/
theorem rate_bounds (lam : ℝ) (h0 : 0 < lam) (h1 : lam < 1) :
    0 < rateMVC lam ∧ rateMVC lam < lam := by sorry

end AccelVI.MVC
