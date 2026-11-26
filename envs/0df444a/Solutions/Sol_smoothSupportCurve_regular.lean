-- Prove2me | solution 1 for smoothSupportCurve_regular
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:23:53.343243+00:00
-- url     : https://prove2.me/submissions/3605208a-0735-43ed-a676-5e2000bd2966

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
    deriv (smoothSupportCurve h) theta ≠ 0 := by
  rw [deriv_smoothSupportCurve hsmooth]
  exact smul_ne_zero (hcurv theta).ne' (by
    unfold smoothSupportUnitTangent smoothSupportUnitNormal
    rw [mul_ne_zero_iff_right I_ne_zero]
    intro hzero
    have hnorm := congrArg norm hzero
    rw [norm_circleMap_zero, abs_one, norm_zero] at hnorm
    exact one_ne_zero hnorm)
