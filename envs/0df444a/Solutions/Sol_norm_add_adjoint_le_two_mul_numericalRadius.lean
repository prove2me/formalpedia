-- Prove2me | solution 1 for norm_add_adjoint_le_two_mul_numericalRadius
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:02:57.680908+00:00
-- url     : https://prove2.me/submissions/254ebc6a-50d2-4c33-ade3-3770188e99c8

import Definitions.Def_Operator_NumericalRange_RadiusAdjoint
import Definitions.Def_Operator_NumericalRange_RadiusNormal
import Definitions.Def_Operator_NumericalRange_RadiusCartesian
import Theorems.Thm_numericalRadius_adjoint
import Theorems.Thm_numericalRadius_eq_norm_of_isSelfAdjoint
attribute [local simp] numericalRadius_adjoint



set_option autoImplicit false
open Complex ContinuousLinearMap
open scoped InnerProductSpace InnerProduct
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution (A : E →L[ℂ] E) :
    ‖A + A†‖ ≤ 2 * numericalRadius A := by
  have hself : IsSelfAdjoint (A + A†) := IsSelfAdjoint.add_star_self A
  rw [← numericalRadius_eq_norm_of_isSelfAdjoint (A + A†) hself]
  calc
    numericalRadius (A + A†) ≤ numericalRadius A + numericalRadius (A†) :=
      numericalRadius_add_le A (A†)
    _ = 2 * numericalRadius A := by rw [numericalRadius_adjoint]; ring
