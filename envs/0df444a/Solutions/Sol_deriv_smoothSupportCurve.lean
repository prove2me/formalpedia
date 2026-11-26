-- Prove2me | solution 1 for deriv_smoothSupportCurve
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:11:34.437942+00:00
-- url     : https://prove2.me/submissions/fb64e068-dfe9-40a8-890e-9f7cf608cb8d

import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupportCurvature
import Definitions.Def_Operator_Crouzeix_SmoothSupportCurve
import Theorems.Thm_contDiff_smoothSupportUnitNormal
import Theorems.Thm_contDiff_smoothSupportUnitTangent
import Theorems.Thm_deriv_smoothSupportUnitNormal
import Theorems.Thm_deriv_smoothSupportUnitTangent

set_option autoImplicit false
open Complex Set
open scoped ContDiff
theorem _root_.solution {h : ℝ → ℝ}
    (hsmooth : ContDiff ℝ ∞ h) (theta : ℝ) :
    deriv (smoothSupportCurve h) theta =
      smoothSupportCurvatureRadius h theta •
        smoothSupportUnitTangent theta := by
  have hderivSmooth : ContDiff ℝ ∞ (deriv h) :=
    (contDiff_infty_iff_deriv.mp hsmooth).2
  have hh := hsmooth.differentiable (by norm_num) theta
  have hdh := hderivSmooth.differentiable (by norm_num) theta
  have hn := contDiff_smoothSupportUnitNormal.differentiable (by norm_num) theta
  have ht := contDiff_smoothSupportUnitTangent.differentiable (by norm_num) theta
  change deriv
      (h • smoothSupportUnitNormal + deriv h • smoothSupportUnitTangent) theta = _
  rw [deriv_add (hh.smul hn) (hdh.smul ht),
    deriv_smul hh hn, deriv_smul hdh ht,
    deriv_smoothSupportUnitNormal, deriv_smoothSupportUnitTangent]
  unfold smoothSupportCurvatureRadius
  module
