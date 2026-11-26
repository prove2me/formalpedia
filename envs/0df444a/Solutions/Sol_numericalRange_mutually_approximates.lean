-- Prove2me | solution 1 for numericalRange_mutually_approximates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:45:47.274881+00:00
-- url     : https://prove2.me/submissions/ae57a9e8-9c44-48ee-b0f1-e47a8f648052

import Definitions.Def_Operator_NumericalRange_Bounded
import Definitions.Def_Operator_NumericalRange_Stability
import Theorems.Thm_exists_mem_numericalRange_norm_sub_le_norm_sub

set_option autoImplicit false
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution
    (A B : E →L[ℂ] E) :
    (∀ z ∈ numericalRange A,
        ∃ w ∈ numericalRange B, ‖z - w‖ ≤ ‖A - B‖) ∧
      (∀ w ∈ numericalRange B,
        ∃ z ∈ numericalRange A, ‖w - z‖ ≤ ‖A - B‖) := by
  constructor
  · exact fun _ hz => exists_mem_numericalRange_norm_sub_le_norm_sub A B hz
  · intro w hw
    obtain ⟨z, hz, hdist⟩ :=
      exists_mem_numericalRange_norm_sub_le_norm_sub B A hw
    refine ⟨z, hz, ?_⟩
    exact hdist.trans_eq (norm_sub_rev B A)
