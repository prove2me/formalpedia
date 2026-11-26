-- Prove2me | solution 1 for polytopeRoundedSupportCurve_mem_smoothSupportClosedEnvelope
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:29:02.783851+00:00
-- url     : https://prove2.me/submissions/b9f74e08-621a-4f46-8873-d5053983cc55

import Definitions.Def_Operator_Crouzeix_SmoothSupportCurve
import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelopeApproximation
import Definitions.Def_Operator_Crouzeix_SmoothSupportCurveGlobal
import Theorems.Thm_polytopeDirectionalValue_smoothSupportCurve_le
import Theorems.Thm_contDiff_polytopeRoundedSupport
import Theorems.Thm_periodic_polytopeRoundedSupport
import Theorems.Thm_polytopeRoundedSupport_add_deriv_deriv_pos


set_option autoImplicit false
open Complex Metric Set
open scoped ContDiff
theorem _root_.solution
    {u : Finset ℂ} (hu : u.Nonempty) {delta rho : ℝ}
    (hdelta : 0 < delta) (hrho : 0 < rho) (theta : ℝ) :
    polytopeRoundedSupportCurve u delta rho theta ∈
      smoothSupportClosedEnvelope (polytopeRoundedSupport u delta rho) := by
  intro phi
  exact polytopeDirectionalValue_smoothSupportCurve_le
    (contDiff_polytopeRoundedSupport hu delta rho)
    (periodic_polytopeRoundedSupport u delta rho)
    (fun x => by
      unfold smoothSupportCurvatureRadius
      exact polytopeRoundedSupport_add_deriv_deriv_pos
        hu hdelta hrho x)
    phi theta
