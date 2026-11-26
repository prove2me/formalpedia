-- Prove2me | solution 1 for norm_aeval_le_polynomialSupNorm_numericalRange_of_isStarNormal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:47:00.655605+00:00
-- url     : https://prove2.me/submissions/65a49c7f-25ed-494e-ac86-1cb8ac31c4cc

import Definitions.Def_Operator_Crouzeix_PolynomialBound
import Definitions.Def_Operator_NumericalRange_RadiusNormal
import Definitions.Def_Operator_SpectralSet_Normal
import Definitions.Def_Operator_Crouzeix_NormalPolynomialBound
import Theorems.Thm_isBounded_numericalRange
import Theorems.Thm_norm_aeval_le_polynomialSupNorm_of_isStarNormal
import Theorems.Thm_polynomialSupNorm_closure_numericalRange
import Theorems.Thm_spectrum_subset_closure_numericalRange


set_option autoImplicit false
open Complex Set
open scoped InnerProductSpace Polynomial
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) [IsStarNormal A] (p : ℂ[X]) :
    ‖Polynomial.aeval A p‖ ≤ polynomialSupNorm p (numericalRange A) := by
  rw [← polynomialSupNorm_closure_numericalRange A p]
  exact
    norm_aeval_le_polynomialSupNorm_of_isStarNormal A
      (isBounded_numericalRange A).isCompact_closure
      (spectrum_subset_closure_numericalRange A) p
