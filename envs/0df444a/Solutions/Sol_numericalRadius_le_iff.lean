-- Prove2me | solution 1 for numericalRadius_le_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:15:10.980987+00:00
-- url     : https://prove2.me/submissions/04ed1619-b4be-4aec-a3e6-aa06ebf7e307

import Definitions.Def_Operator_NumericalRange_Radius
import Definitions.Def_Operator_NumericalRange_RadiusCharacterization
import Theorems.Thm_norm_le_numericalRadius


set_option autoImplicit false
open Set
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution
    (A : E →L[ℂ] E) {r : ℝ} (hr : 0 ≤ r) :
    numericalRadius A ≤ r ↔ ∀ z ∈ numericalRange A, ‖z‖ ≤ r := by
  constructor
  · exact fun h z hz => (norm_le_numericalRadius A hz).trans h
  · intro h
    unfold numericalRadius
    exact Real.iSup_le (fun z => Real.iSup_le (fun hz => h z hz) hr) hr
