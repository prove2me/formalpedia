-- Prove2me | solution 1 for exists_active_direction_of_mem_frontier_smoothSupportOpenEnvelope
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:32:19.62774+00:00
-- url     : https://prove2.me/submissions/54869ca9-e2a7-4cbe-b844-97bc1473ae24

import Definitions.Def_Operator_Crouzeix_SmoothSupportCurveGlobal
import Definitions.Def_Operator_Crouzeix_SmoothSupportCurveRange
import Theorems.Thm_mem_smoothSupportOpenEnvelope_of_forall_lt
import Theorems.Thm_isClosed_smoothSupportClosedEnvelope
import Theorems.Thm_isOpen_smoothSupportOpenEnvelope


set_option autoImplicit false
open Complex Metric Set
open scoped ContDiff
theorem _root_.solution
    {h : ℝ → ℝ} (hcontinuous : Continuous h)
    (hperiodic : Function.Periodic h (2 * Real.pi)) {z : ℂ}
    (hz : z ∈ frontier (smoothSupportOpenEnvelope h)) :
    ∃ theta, polytopeDirectionalValue z theta = h theta := by
  rw [(isOpen_smoothSupportOpenEnvelope h).frontier_eq] at hz
  have hclosureSubset :
      closure (smoothSupportOpenEnvelope h) ⊆
        smoothSupportClosedEnvelope h := by
    apply closure_minimal
    · exact interior_subset
    · exact isClosed_smoothSupportClosedEnvelope h
  have hzclosed := hclosureSubset hz.1
  by_contra hnone
  have hzstrict (theta : ℝ) :
      polytopeDirectionalValue z theta < h theta := by
    exact lt_of_le_of_ne (hzclosed theta) (fun heq =>
      hnone ⟨theta, heq⟩)
  exact hz.2
    (mem_smoothSupportOpenEnvelope_of_forall_lt
      hcontinuous hperiodic hzstrict)
