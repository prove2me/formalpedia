-- Prove2me | solution 1 for norm_deriv_smoothSupportCurve
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:25:44.984315+00:00
-- url     : https://prove2.me/submissions/a72bcaa7-29e9-472f-a35c-76c1ac2a3412

import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupportCurvature
import Definitions.Def_Operator_Crouzeix_SmoothSupportCurve
import Theorems.Thm_deriv_smoothSupportCurve

set_option autoImplicit false
open Complex Set
open scoped ContDiff
theorem _root_.solution {h : ℝ → ℝ}
    (hsmooth : ContDiff ℝ ∞ h)
    (hcurv : ∀ theta, 0 < smoothSupportCurvatureRadius h theta)
    (theta : ℝ) :
    ‖deriv (smoothSupportCurve h) theta‖ =
      smoothSupportCurvatureRadius h theta := by
  rw [deriv_smoothSupportCurve hsmooth, norm_smul, Real.norm_eq_abs,
    abs_of_pos (hcurv theta)]
  unfold smoothSupportUnitTangent smoothSupportUnitNormal
  rw [norm_mul, norm_circleMap_zero, norm_I, abs_one, one_mul]
  exact mul_one _
