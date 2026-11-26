-- Prove2me | solution 1 for numericalRadius_pow_le_two_mul_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:45:14.105734+00:00
-- url     : https://prove2.me/submissions/fe7497eb-55ae-42a7-9be8-8b43cc45e2a5

import Mathlib.Analysis.Normed.Operator.Mul
import Definitions.Def_Operator_NumericalRange_Radius
import Definitions.Def_Operator_NumericalRange_RadiusAlgebra
import Theorems.Thm_numericalRadius_le_norm


set_option autoImplicit false
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution
    [Nontrivial E] (A : E →L[ℂ] E) (n : ℕ) :
    numericalRadius (A ^ n) ≤ (2 * numericalRadius A) ^ n := by
  calc
    numericalRadius (A ^ n) ≤ ‖A ^ n‖ := numericalRadius_le_norm (A ^ n)
    _ ≤ ‖A‖ ^ n := norm_pow_le A n
    _ ≤ (2 * numericalRadius A) ^ n :=
      pow_le_pow_left₀ (norm_nonneg A)
        (norm_le_two_mul_numericalRadius A) n
