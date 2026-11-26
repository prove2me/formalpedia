-- Prove2me | solution 1 for numericalRadius_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:07:59.097881+00:00
-- url     : https://prove2.me/submissions/de699c95-8ce8-43fe-90ae-73abb8794b08

import Definitions.Def_Operator_NumericalRange_Adjoint
import Definitions.Def_Operator_NumericalRange_Radius
import Definitions.Def_Operator_NumericalRange_RadiusAdjoint
import Theorems.Thm_numericalRadius_adjoint_le
import Theorems.Thm_mem_numericalRange
import Theorems.Thm_numericalRadiusSeminorm_apply
import Theorems.Thm_numericalRadius_neg
attribute [local simp] mem_numericalRange
attribute [local simp] numericalRadiusSeminorm_apply
attribute [local simp] numericalRadius_neg



set_option autoImplicit false
open Complex
open ContinuousLinearMap
open scoped InnerProductSpace InnerProduct
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution (A : E →L[ℂ] E) :
    numericalRadius (A†) = numericalRadius A := by
  apply le_antisymm (numericalRadius_adjoint_le A)
  simpa only [adjoint_adjoint] using numericalRadius_adjoint_le (A†)
