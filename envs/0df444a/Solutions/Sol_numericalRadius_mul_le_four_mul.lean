-- Prove2me | solution 1 for numericalRadius_mul_le_four_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:15:26.118098+00:00
-- url     : https://prove2.me/submissions/79436103-1d77-4e4c-985c-23cc1ebd9c3c

import Mathlib.Analysis.Normed.Operator.Mul
import Definitions.Def_Operator_NumericalRange_Radius
import Definitions.Def_Operator_NumericalRange_RadiusAlgebra
import Theorems.Thm_numericalRadius_mul_le_two_mul_numericalRadius_mul_norm
import Theorems.Thm_numericalRadius_nonneg


set_option autoImplicit false
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution
    (A B : E →L[ℂ] E) :
    numericalRadius (A * B) ≤
      4 * numericalRadius A * numericalRadius B := by
  calc
    numericalRadius (A * B) ≤ 2 * numericalRadius A * ‖B‖ :=
      numericalRadius_mul_le_two_mul_numericalRadius_mul_norm A B
    _ ≤ (2 * numericalRadius A) * (2 * numericalRadius B) :=
      mul_le_mul_of_nonneg_left (norm_le_two_mul_numericalRadius B)
        (mul_nonneg zero_le_two (numericalRadius_nonneg A))
    _ = 4 * numericalRadius A * numericalRadius B := by ring
