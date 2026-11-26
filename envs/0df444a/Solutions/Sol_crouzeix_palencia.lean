-- Prove2me | solution 1 for crouzeix_palencia
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:54:19.978672+00:00
-- url     : https://prove2.me/submissions/31a6f3c6-2ddf-4604-b163-2f9b0dfde363

import Definitions.Def_Operator_Crouzeix_SmoothSupportCurveRange
import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelopeTight
import Definitions.Def_Operator_Crouzeix_SmoothSupportDomain
import Theorems.Thm_hasSmoothJordanOuterApproximationForPolytopes
import Theorems.Thm_crouzeix_palencia_of_smoothJordanOuterApproximation_polytope_case
import Theorems.Thm_polynomialSupNorm_nonneg
import Theorems.Thm_spectrum_subset_closure_numericalRange


set_option autoImplicit false
open Complex Metric Set
open scoped ContDiff InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution (A : E →L[ℂ] E) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · let _ := hE
    constructor
    · exact spectrum_subset_closure_numericalRange A
    · intro p
      have hzero : Polynomial.aeval A p = 0 := Subsingleton.elim _ _
      rw [hzero, norm_zero]
      exact mul_nonneg
        (add_nonneg zero_le_one (Real.sqrt_nonneg 2))
        (polynomialSupNorm_nonneg p (closure (numericalRange A)))
  · let _ := hE
    exact
      crouzeix_palencia_of_smoothJordanOuterApproximation_polytope_case
        A hasSmoothJordanOuterApproximationForPolytopes
