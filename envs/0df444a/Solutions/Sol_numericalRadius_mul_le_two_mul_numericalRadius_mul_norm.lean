-- Prove2me | solution 1 for numericalRadius_mul_le_two_mul_numericalRadius_mul_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:14:30.50444+00:00
-- url     : https://prove2.me/submissions/b04a95d9-680d-477a-88cd-3df27f3672aa

import Mathlib.Analysis.Normed.Operator.Mul
import Definitions.Def_Operator_NumericalRange_Radius
import Definitions.Def_Operator_NumericalRange_RadiusAlgebra
import Theorems.Thm_numericalRadius_mul_le_norm_mul_norm

set_option autoImplicit false
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution
    (A B : E →L[ℂ] E) :
    numericalRadius (A * B) ≤ 2 * numericalRadius A * ‖B‖ := by
  exact (numericalRadius_mul_le_norm_mul_norm A B).trans
    (mul_le_mul_of_nonneg_right
      (norm_le_two_mul_numericalRadius A) (norm_nonneg B))
