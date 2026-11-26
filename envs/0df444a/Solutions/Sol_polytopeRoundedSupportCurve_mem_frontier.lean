-- Prove2me | solution 1 for polytopeRoundedSupportCurve_mem_frontier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:31:27.277027+00:00
-- url     : https://prove2.me/submissions/c4d7a7d8-eca9-40ef-8393-39f30a69a6b1

import Definitions.Def_Operator_Crouzeix_SmoothSupportCurve
import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelopeApproximation
import Definitions.Def_Operator_Crouzeix_SmoothSupportCurveGlobal
import Theorems.Thm_smoothSupportCurve_not_mem_smoothSupportOpenEnvelope
import Theorems.Thm_polytopeRoundedSupportCurve_mem_smoothSupportClosedEnvelope
import Theorems.Thm_closure_smoothSupportOpenEnvelope_polytopeRoundedSupport
import Theorems.Thm_isOpen_smoothSupportOpenEnvelope


set_option autoImplicit false
open Complex Metric Set
open scoped ContDiff
theorem _root_.solution
    {u : Finset ℂ} (hu : u.Nonempty) {delta rho : ℝ}
    (hdelta : 0 < delta) (hrho : 0 < rho) (theta : ℝ) :
    polytopeRoundedSupportCurve u delta rho theta ∈
      frontier
        (smoothSupportOpenEnvelope (polytopeRoundedSupport u delta rho)) := by
  rw [(isOpen_smoothSupportOpenEnvelope _).frontier_eq]
  constructor
  · rw [closure_smoothSupportOpenEnvelope_polytopeRoundedSupport
      hu hdelta hrho]
    exact polytopeRoundedSupportCurve_mem_smoothSupportClosedEnvelope
      hu hdelta hrho theta
  · exact smoothSupportCurve_not_mem_smoothSupportOpenEnvelope
      (polytopeRoundedSupport u delta rho) theta
