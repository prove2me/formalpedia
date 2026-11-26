-- Prove2me | solution 1 for numericalRadius_anticommutator_le_eight_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:45:35.266396+00:00
-- url     : https://prove2.me/submissions/ad632338-3e62-4295-b55e-2ff80c4804df

import Mathlib.Analysis.Normed.Operator.Mul
import Definitions.Def_Operator_NumericalRange_Radius
import Definitions.Def_Operator_NumericalRange_RadiusAlgebra
import Theorems.Thm_numericalRadius_mul_le_four_mul

set_option autoImplicit false
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution
    (A B : E →L[ℂ] E) :
    numericalRadius (A * B + B * A) ≤
      8 * numericalRadius A * numericalRadius B := by
  calc
    numericalRadius (A * B + B * A) ≤
        numericalRadius (A * B) + numericalRadius (B * A) :=
      numericalRadius_add_le (A * B) (B * A)
    _ ≤ 4 * numericalRadius A * numericalRadius B +
        4 * numericalRadius B * numericalRadius A :=
      add_le_add (numericalRadius_mul_le_four_mul A B)
        (numericalRadius_mul_le_four_mul B A)
    _ = 8 * numericalRadius A * numericalRadius B := by ring
