-- Prove2me | solution 1 for neg_I_mul_deriv_smoothSupportCurve
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:25:49.558879+00:00
-- url     : https://prove2.me/submissions/b6ddb151-8a23-4696-b173-4c5678bcca4d

import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupportCurvature
import Definitions.Def_Operator_Crouzeix_SmoothSupportCurve
import Theorems.Thm_deriv_smoothSupportCurve

set_option autoImplicit false
open Complex Set
open scoped ContDiff
theorem _root_.solution {h : ℝ → ℝ}
    (hsmooth : ContDiff ℝ ∞ h) (theta : ℝ) :
    -I * deriv (smoothSupportCurve h) theta =
      smoothSupportCurvatureRadius h theta •
        smoothSupportUnitNormal theta := by
  rw [deriv_smoothSupportCurve hsmooth]
  unfold smoothSupportUnitTangent
  change -I * ((smoothSupportCurvatureRadius h theta : ℂ) *
      (smoothSupportUnitNormal theta * I)) =
    (smoothSupportCurvatureRadius h theta : ℂ) *
      smoothSupportUnitNormal theta
  ring_nf
  rw [I_sq]
  ring
