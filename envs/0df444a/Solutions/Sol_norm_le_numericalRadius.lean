-- Prove2me | solution 1 for norm_le_numericalRadius
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:14:58.011804+00:00
-- url     : https://prove2.me/submissions/6f22bbcf-580c-4350-8648-7ca1cbfd3a16

import Mathlib.Analysis.Normed.Operator.Basic
import Definitions.Def_Operator_NumericalRange_Basic
import Definitions.Def_Operator_NumericalRange_Bounded
import Theorems.Thm_norm_le_of_mem_numericalRange

set_option autoImplicit false
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution (A : E →L[ℂ] E)
    {z : ℂ} (hz : z ∈ numericalRange A) : ‖z‖ ≤ numericalRadius A := by
  unfold numericalRadius
  refine le_ciSup₂
    (f := fun z (_ : z ∈ numericalRange A) => ‖z‖) ⟨‖A‖, ?_⟩ z hz
  rintro y hy
  rw [Set.mem_iUnion] at hy
  obtain ⟨w, hw⟩ := hy
  rw [Set.mem_range] at hw
  obtain ⟨hwA, rfl⟩ := hw
  exact norm_le_of_mem_numericalRange A hwA
