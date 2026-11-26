-- Prove2me | solution 1 for norm_aeval_le_one_add_sqrt_two_mul_polynomialSupNorm_numericalRange
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:57:24.47805+00:00
-- url     : https://prove2.me/submissions/99793f9b-372d-4248-b6bd-1fab3da1fccb

import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_Operator_Crouzeix_BoundaryMaximum
import Definitions.Def_Operator_Crouzeix_SmoothSupportDomain
import Definitions.Def_Operator_Crouzeix_PolynomialBound
import Theorems.Thm_polynomialSupNorm_closure_numericalRange
import Theorems.Thm_crouzeix_palencia


set_option autoImplicit false
open Complex Set
open scoped InnerProductSpace Polynomial
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) (p : ℂ[X]) :
    ‖Polynomial.aeval A p‖ ≤
      (1 + Real.sqrt 2) * polynomialSupNorm p (numericalRange A) := by
  rw [← polynomialSupNorm_closure_numericalRange A p]
  exact (crouzeix_palencia A).2 p
