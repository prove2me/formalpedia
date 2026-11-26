-- Prove2me | solution 1 for norm_pow_le_one_of_isStarNormal_of_numericalRadius_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:31:28.022886+00:00
-- url     : https://prove2.me/submissions/2d0057e3-ee9f-4d9c-bb47-138510dbbf56

import Definitions.Def_Operator_Crouzeix_PolynomialBound
import Definitions.Def_Operator_NumericalRange_RadiusNormal
import Definitions.Def_Operator_SpectralSet_Normal
import Definitions.Def_Operator_Crouzeix_NormalPolynomialBound
import Theorems.Thm_norm_pow_le_numericalRadius_pow_of_isStarNormal
import Theorems.Thm_numericalRadius_nonneg


set_option autoImplicit false
open Complex Set
open scoped InnerProductSpace Polynomial
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) [IsStarNormal A]
    (hA : numericalRadius A ≤ 1) (n : ℕ) :
    ‖A ^ n‖ ≤ 1 := by
  exact (norm_pow_le_numericalRadius_pow_of_isStarNormal A n).trans
    (pow_le_one₀ (numericalRadius_nonneg A) hA)
