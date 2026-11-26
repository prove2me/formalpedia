-- Prove2me | solution 1 for norm_pow_le_one_add_sqrt_two_mul_numericalRadius_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:01:04.790285+00:00
-- url     : https://prove2.me/submissions/122d50d4-5eab-4dfc-af6f-070fd0f8715c

import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_Operator_Crouzeix_BoundaryMaximum
import Definitions.Def_Operator_Crouzeix_SmoothSupportDomain
import Definitions.Def_Operator_Crouzeix_PolynomialBound
import Theorems.Thm_iSup_norm_pow_numericalRange_le_numericalRadius_pow
import Theorems.Thm_norm_pow_le_one_add_sqrt_two_mul_iSup_numericalRange

set_option autoImplicit false
open Complex Set
open scoped InnerProductSpace Polynomial
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) (n : ℕ) :
    ‖A ^ n‖ ≤ (1 + Real.sqrt 2) * numericalRadius A ^ n := by
  exact (norm_pow_le_one_add_sqrt_two_mul_iSup_numericalRange A n).trans
    (mul_le_mul_of_nonneg_left
      (iSup_norm_pow_numericalRange_le_numericalRadius_pow A n) (by positivity))
