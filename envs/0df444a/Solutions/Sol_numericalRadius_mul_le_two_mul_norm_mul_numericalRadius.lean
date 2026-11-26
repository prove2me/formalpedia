-- Prove2me | solution 1 for numericalRadius_mul_le_two_mul_norm_mul_numericalRadius
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:45:07.164451+00:00
-- url     : https://prove2.me/submissions/8a38518d-a3f1-44e8-926e-9197dbcf27b6

import Mathlib.Analysis.Normed.Operator.Mul
import Definitions.Def_Operator_NumericalRange_Radius
import Definitions.Def_Operator_NumericalRange_RadiusAlgebra
import Theorems.Thm_numericalRadius_mul_le_norm_mul_norm

set_option autoImplicit false
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution
    (A B : E →L[ℂ] E) :
    numericalRadius (A * B) ≤ 2 * ‖A‖ * numericalRadius B := by
  calc
    numericalRadius (A * B) ≤ ‖A‖ * ‖B‖ :=
      numericalRadius_mul_le_norm_mul_norm A B
    _ ≤ ‖A‖ * (2 * numericalRadius B) :=
      mul_le_mul_of_nonneg_left
        (norm_le_two_mul_numericalRadius B) (norm_nonneg A)
    _ = 2 * ‖A‖ * numericalRadius B := by ring
