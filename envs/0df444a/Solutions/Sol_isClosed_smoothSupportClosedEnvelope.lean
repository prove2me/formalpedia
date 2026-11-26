-- Prove2me | solution 1 for isClosed_smoothSupportClosedEnvelope
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:27:14.296187+00:00
-- url     : https://prove2.me/submissions/21f90d40-9980-4e4c-bb00-3b8a32213f90

import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupportCurvature
import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelope
import Theorems.Thm_smoothSupportClosedEnvelope_eq_iInter
import Theorems.Thm_continuous_polytopeDirectionalValue_left

set_option autoImplicit false
open Complex Metric Set
open scoped ComplexConjugate
theorem _root_.solution (h : ℝ → ℝ) :
    IsClosed (smoothSupportClosedEnvelope h) := by
  rw [smoothSupportClosedEnvelope_eq_iInter]
  apply isClosed_iInter
  intro theta
  exact isClosed_le (continuous_polytopeDirectionalValue_left theta)
    continuous_const
