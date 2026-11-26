-- Prove2me | solution 1 for periodic_polytopeRoundedSupportCurve
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:26:03.595403+00:00
-- url     : https://prove2.me/submissions/62ca2ba8-d110-45da-832d-ae5e6514d815

import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupportCurvature
import Definitions.Def_Operator_Crouzeix_SmoothSupportCurve
import Theorems.Thm_periodic_smoothSupportCurve
import Theorems.Thm_periodic_polytopeRoundedSupport


set_option autoImplicit false
open Complex Set
open scoped ContDiff
theorem _root_.solution
    (u : Finset ℂ) (delta rho : ℝ) :
    Function.Periodic (polytopeRoundedSupportCurve u delta rho)
      (2 * Real.pi) := by
  exact periodic_smoothSupportCurve
    (periodic_polytopeRoundedSupport u delta rho)
