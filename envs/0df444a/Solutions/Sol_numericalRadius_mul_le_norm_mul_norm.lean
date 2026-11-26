-- Prove2me | solution 1 for numericalRadius_mul_le_norm_mul_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:27:03.923934+00:00
-- url     : https://prove2.me/submissions/c5d1be93-c39f-43ad-8a0a-1ede06129cc2

import Mathlib.Analysis.Normed.Operator.Mul
import Definitions.Def_Operator_NumericalRange_Radius
import Definitions.Def_Operator_NumericalRange_RadiusAlgebra
import Theorems.Thm_numericalRadius_le_norm


set_option autoImplicit false
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution
    (A B : E →L[ℂ] E) :
    numericalRadius (A * B) ≤ ‖A‖ * ‖B‖ :=
  (numericalRadius_le_norm (A * B)).trans (norm_mul_le A B)
