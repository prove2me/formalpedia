-- Prove2me | solution 1 for range_polytopeRoundedSupportCurve_subset_frontier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:32:46.683871+00:00
-- url     : https://prove2.me/submissions/a921ac1c-8ad6-4afb-a486-c177c389d354

import Definitions.Def_Operator_Crouzeix_SmoothSupportCurve
import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelopeApproximation
import Definitions.Def_Operator_Crouzeix_SmoothSupportCurveGlobal
import Theorems.Thm_polytopeRoundedSupportCurve_mem_frontier

set_option autoImplicit false
open Complex Metric Set
open scoped ContDiff
theorem _root_.solution
    {u : Finset ℂ} (hu : u.Nonempty) {delta rho : ℝ}
    (hdelta : 0 < delta) (hrho : 0 < rho) :
    range (polytopeRoundedSupportCurve u delta rho) ⊆
      frontier
        (smoothSupportOpenEnvelope (polytopeRoundedSupport u delta rho)) := by
  rintro z ⟨theta, rfl⟩
  exact polytopeRoundedSupportCurve_mem_frontier hu hdelta hrho theta
