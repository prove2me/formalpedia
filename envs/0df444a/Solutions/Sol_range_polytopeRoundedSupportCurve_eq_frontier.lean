-- Prove2me | solution 1 for range_polytopeRoundedSupportCurve_eq_frontier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:39:43.738816+00:00
-- url     : https://prove2.me/submissions/d3a0bfa4-46cf-4742-af98-d0728265ae07

import Definitions.Def_Operator_Crouzeix_SmoothSupportCurveGlobal
import Definitions.Def_Operator_Crouzeix_SmoothSupportCurveRange
import Theorems.Thm_frontier_smoothSupportOpenEnvelope_subset_range_smoothSupportCurve
import Theorems.Thm_contDiff_polytopeRoundedSupport
import Theorems.Thm_periodic_polytopeRoundedSupport
import Theorems.Thm_range_polytopeRoundedSupportCurve_subset_frontier


set_option autoImplicit false
open Complex Metric Set
open scoped ContDiff
theorem _root_.solution
    {u : Finset ℂ} (hu : u.Nonempty) {delta rho : ℝ}
    (hdelta : 0 < delta) (hrho : 0 < rho) :
    range (polytopeRoundedSupportCurve u delta rho) =
      frontier
        (smoothSupportOpenEnvelope (polytopeRoundedSupport u delta rho)) := by
  apply Subset.antisymm
  · exact range_polytopeRoundedSupportCurve_subset_frontier
      hu hdelta hrho
  · exact frontier_smoothSupportOpenEnvelope_subset_range_smoothSupportCurve
      (contDiff_polytopeRoundedSupport hu delta rho)
      (periodic_polytopeRoundedSupport u delta rho)
