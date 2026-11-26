-- Prove2me | solution 1 for norm_pow_sub_smul_one_le_one_add_sqrt_two_mul_numericalRadius_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:29:23.468408+00:00
-- url     : https://prove2.me/submissions/75e5e2d2-904d-4dcd-a3de-18fa7f0c8987

import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_Operator_Crouzeix_BoundaryMaximum
import Definitions.Def_Operator_Crouzeix_SmoothSupportDomain
import Definitions.Def_Operator_Crouzeix_PolynomialBound
import Theorems.Thm_norm_pow_le_one_add_sqrt_two_mul_numericalRadius_pow

set_option autoImplicit false
open Complex Set
open scoped InnerProductSpace Polynomial
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) (c : ℂ) (n : ℕ) :
    ‖(A - c • (1 : E →L[ℂ] E)) ^ n‖ ≤
      (1 + Real.sqrt 2) *
        numericalRadius (A - c • (1 : E →L[ℂ] E)) ^ n :=
  norm_pow_le_one_add_sqrt_two_mul_numericalRadius_pow
    (A - c • (1 : E →L[ℂ] E)) n
