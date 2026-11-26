-- Prove2me | solution 1 for frontier_smoothSupportOpenEnvelope_subset_range_smoothSupportCurve
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:38:43.463128+00:00
-- url     : https://prove2.me/submissions/9f428dbd-f236-4181-b451-df7b110cee94

import Definitions.Def_Operator_Crouzeix_SmoothSupportCurveGlobal
import Definitions.Def_Operator_Crouzeix_SmoothSupportCurveRange
import Theorems.Thm_eq_smoothSupportCurve_of_mem_closedEnvelope_of_eq
import Theorems.Thm_exists_active_direction_of_mem_frontier_smoothSupportOpenEnvelope
import Theorems.Thm_isClosed_smoothSupportClosedEnvelope


set_option autoImplicit false
open Complex Metric Set
open scoped ContDiff
theorem _root_.solution
    {h : ℝ → ℝ} (hsmooth : ContDiff ℝ ∞ h)
    (hperiodic : Function.Periodic h (2 * Real.pi)) :
    frontier (smoothSupportOpenEnvelope h) ⊆ range (smoothSupportCurve h) := by
  intro z hz
  obtain ⟨theta, hactive⟩ :=
    exists_active_direction_of_mem_frontier_smoothSupportOpenEnvelope
      hsmooth.continuous hperiodic hz
  have hclosureSubset :
      closure (smoothSupportOpenEnvelope h) ⊆
        smoothSupportClosedEnvelope h := by
    apply closure_minimal
    · exact interior_subset
    · exact isClosed_smoothSupportClosedEnvelope h
  have hzclosed : z ∈ smoothSupportClosedEnvelope h := by
    exact hclosureSubset (frontier_subset_closure hz)
  refine ⟨theta, ?_⟩
  exact (eq_smoothSupportCurve_of_mem_closedEnvelope_of_eq
    hsmooth hzclosed hactive).symm
