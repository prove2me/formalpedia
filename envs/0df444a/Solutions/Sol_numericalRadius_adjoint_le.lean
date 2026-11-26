-- Prove2me | solution 1 for numericalRadius_adjoint_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:07:08.687482+00:00
-- url     : https://prove2.me/submissions/73058c65-9a78-457f-aa5d-a62e4d45ca7b

import Definitions.Def_Operator_NumericalRange_Adjoint
import Definitions.Def_Operator_NumericalRange_Radius
import Definitions.Def_Operator_NumericalRange_RadiusAdjoint
import Theorems.Thm_norm_le_numericalRadius
import Theorems.Thm_numericalRadius_nonneg
import Theorems.Thm_numericalRange_adjoint


set_option autoImplicit false
open Complex
open ContinuousLinearMap
open scoped InnerProductSpace InnerProduct
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution (A : E →L[ℂ] E) :
    numericalRadius (A†) ≤ numericalRadius A := by
  unfold numericalRadius
  refine Real.iSup_le (fun z => ?_) (numericalRadius_nonneg A)
  refine Real.iSup_le (fun hz => ?_) (numericalRadius_nonneg A)
  rw [numericalRange_adjoint A] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  rw [starRingEnd_apply, norm_star]
  exact norm_le_numericalRadius A hw
