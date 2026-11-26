-- Prove2me | solution 1 for norm_pow_le_one_add_sqrt_two_of_numericalRadius_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:02:25.418878+00:00
-- url     : https://prove2.me/submissions/c7c6f85f-8979-47d2-bb85-ac7398386f91

import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_Operator_Crouzeix_BoundaryMaximum
import Definitions.Def_Operator_Crouzeix_SmoothSupportDomain
import Definitions.Def_Operator_Crouzeix_PolynomialBound
import Theorems.Thm_norm_pow_le_one_add_sqrt_two_mul_numericalRadius_pow
import Theorems.Thm_numericalRadius_nonneg


set_option autoImplicit false
open Complex Set
open scoped InnerProductSpace Polynomial
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) (hA : numericalRadius A ≤ 1) (n : ℕ) :
    ‖A ^ n‖ ≤ 1 + Real.sqrt 2 := by
  calc
    ‖A ^ n‖ ≤ (1 + Real.sqrt 2) * numericalRadius A ^ n :=
      norm_pow_le_one_add_sqrt_two_mul_numericalRadius_pow A n
    _ ≤ (1 + Real.sqrt 2) * 1 := mul_le_mul_of_nonneg_left
      (pow_le_one₀ (numericalRadius_nonneg A) hA) (by positivity)
    _ = 1 + Real.sqrt 2 := mul_one _
