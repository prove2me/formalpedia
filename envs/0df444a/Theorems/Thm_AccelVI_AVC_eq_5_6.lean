-- Prove2me | Theorems.Thm_AccelVI_AVC_eq_5_6
-- name    : AccelVI.AVC.eq_5_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T09:03:21.044338+00:00
-- url     : https://prove2.me/theorems/b10ed894-ada2-45ae-9197-eed183c40849
-- title:
--   (5.6), p. 9 — λ = 1 − √(1/κ) + √(1−λ)(1 − √(1−λ²))/√(1+λ), with the last term positive
-- statement:
--   Let $\lambda\in(0,1)$ and $\kappa=(1+\lambda)/(1-\lambda)$. Then
--   $$\lambda=1-\sqrt{1/\kappa}+\frac{\sqrt{1-\lambda}\,\big(1-\sqrt{1-\lambda^2}\big)}{\sqrt{1+\lambda}},$$
--   and
--   $$\sqrt{1-\lambda}\,\big(1-\sqrt{1-\lambda^2}\big)>0.$$
--
--   Hence $1-\sqrt{1/\kappa}<\lambda$: the rate of A-VC is strictly better than the rate $\lambda$ of plain value computation.
-- source:
--   Goyal & Grand-Clément, A First-Order Approach to Accelerated Value Iteration, arXiv:1905.09963v7, p. 9, proof of Theorem 5.1, display (5.6) and the line after it

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_AccelVI_AVC_Setting

namespace AccelVI.AVC

/-- (5.6), p. 9: for λ ∈ (0, 1),
`λ = 1 − √(1/κ) + √(1 − λ)(1 − √(1 − λ²))/√(1 + λ)` and `√(1 − λ)(1 − √(1 − λ²)) > 0`. -/
theorem eq_5_6 (lam : ℝ) (h0 : 0 < lam) (h1 : lam < 1) :
    lam = theta lam + Real.sqrt (1 - lam) * (1 - Real.sqrt (1 - lam ^ 2)) / Real.sqrt (1 + lam) ∧
    0 < Real.sqrt (1 - lam) * (1 - Real.sqrt (1 - lam ^ 2)) := by sorry

end AccelVI.AVC
