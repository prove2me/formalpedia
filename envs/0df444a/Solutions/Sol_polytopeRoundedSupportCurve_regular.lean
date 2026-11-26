-- Prove2me | solution 1 for polytopeRoundedSupportCurve_regular
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:28:51.578654+00:00
-- url     : https://prove2.me/submissions/21574cbe-601c-4d6e-a3c5-edf967e8cf74

import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupportCurvature
import Definitions.Def_Operator_Crouzeix_SmoothSupportCurve
import Theorems.Thm_smoothSupportCurve_regular
import Theorems.Thm_contDiff_polytopeRoundedSupport
import Theorems.Thm_polytopeRoundedSupport_add_deriv_deriv_pos


set_option autoImplicit false
open Complex Set
open scoped ContDiff
theorem _root_.solution
    {u : Finset ℂ} (hu : u.Nonempty) {delta rho : ℝ}
    (hdelta : 0 < delta) (hrho : 0 < rho) (theta : ℝ) :
    deriv (polytopeRoundedSupportCurve u delta rho) theta ≠ 0 := by
  apply smoothSupportCurve_regular
    (contDiff_polytopeRoundedSupport hu delta rho)
  intro x
  unfold smoothSupportCurvatureRadius
  exact polytopeRoundedSupport_add_deriv_deriv_pos
    hu hdelta hrho x
