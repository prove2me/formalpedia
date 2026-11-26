-- Prove2me | solution 1 for periodic_smoothSupportCurve
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:24:27.403846+00:00
-- url     : https://prove2.me/submissions/1727f274-5561-4b44-9657-d728731649d1

import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupportCurvature
import Definitions.Def_Operator_Crouzeix_SmoothSupportCurve
import Theorems.Thm_periodic_deriv_of_periodic
import Theorems.Thm_periodic_smoothSupportUnitNormal
import Theorems.Thm_periodic_smoothSupportUnitTangent

set_option autoImplicit false
open Complex Set
open scoped ContDiff
theorem _root_.solution {h : ℝ → ℝ}
    (hperiodic : Function.Periodic h (2 * Real.pi)) :
    Function.Periodic (smoothSupportCurve h) (2 * Real.pi) := by
  intro theta
  unfold smoothSupportCurve
  rw [hperiodic theta,
    (periodic_deriv_of_periodic hperiodic) theta,
    periodic_smoothSupportUnitNormal theta,
    periodic_smoothSupportUnitTangent theta]
