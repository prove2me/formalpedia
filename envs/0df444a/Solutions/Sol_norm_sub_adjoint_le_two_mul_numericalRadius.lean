-- Prove2me | solution 1 for norm_sub_adjoint_le_two_mul_numericalRadius
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:02:00.302308+00:00
-- url     : https://prove2.me/submissions/fd4791e4-58e3-48e7-a519-75126ab45a88

import Definitions.Def_Operator_NumericalRange_RadiusAdjoint
import Definitions.Def_Operator_NumericalRange_RadiusNormal
import Definitions.Def_Operator_NumericalRange_RadiusCartesian
import Theorems.Thm_mem_numericalRange
import Theorems.Thm_numericalRadiusSeminorm_apply
import Theorems.Thm_numericalRadius_adjoint
import Theorems.Thm_numericalRadius_eq_norm_of_isStarNormal
import Theorems.Thm_numericalRadius_neg
import Theorems.Thm_numericalRadius_sub_le
import Theorems.Thm_numericalRange_scalar
import Theorems.Thm_numericalRange_zero
attribute [local simp] mem_numericalRange
attribute [local simp] numericalRadiusSeminorm_apply
attribute [local simp] numericalRadius_adjoint
attribute [local simp] numericalRadius_neg
attribute [local simp] numericalRange_scalar
attribute [local simp] numericalRange_zero



set_option autoImplicit false
open Complex ContinuousLinearMap
open scoped InnerProductSpace InnerProduct
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution (A : E →L[ℂ] E) :
    ‖A - A†‖ ≤ 2 * numericalRadius A := by
  have hskew' : A - star A ∈ skewAdjoint (E →L[ℂ] E) := by
    rw [skewAdjoint.mem_iff]
    rw [star_sub, star_star]
    module
  have hskew : A - A† ∈ skewAdjoint (E →L[ℂ] E) := by
    simpa only [star_eq_adjoint] using hskew'
  let _ : IsStarNormal (A - A†) :=
    skewAdjoint.isStarNormal_of_mem hskew
  calc
    ‖A - A†‖ = numericalRadius (A - A†) :=
      (numericalRadius_eq_norm_of_isStarNormal (A - A†)).symm
    _ ≤ numericalRadius A + numericalRadius (A†) :=
      numericalRadius_sub_le A (A†)
    _ = 2 * numericalRadius A := by rw [numericalRadius_adjoint]; ring
