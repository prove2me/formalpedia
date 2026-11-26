-- Prove2me | solution 1 for norm_pow_sub_smul_one_le_one_add_sqrt_two_of_numericalRadius_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:29:24.256584+00:00
-- url     : https://prove2.me/submissions/ad6f4c55-a74b-4a64-81cb-fb338ccacb6b

import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_Operator_Crouzeix_BoundaryMaximum
import Definitions.Def_Operator_Crouzeix_SmoothSupportDomain
import Definitions.Def_Operator_Crouzeix_PolynomialBound
import Theorems.Thm_norm_pow_le_one_add_sqrt_two_of_numericalRadius_le_one

set_option autoImplicit false
open Complex Set
open scoped InnerProductSpace Polynomial
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) (c : ℂ)
    (hA : numericalRadius (A - c • (1 : E →L[ℂ] E)) ≤ 1) (n : ℕ) :
    ‖(A - c • (1 : E →L[ℂ] E)) ^ n‖ ≤ 1 + Real.sqrt 2 :=
  norm_pow_le_one_add_sqrt_two_of_numericalRadius_le_one
    (A - c • (1 : E →L[ℂ] E)) hA n
