-- Prove2me | solution 1 for norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_le_polynomialSupNorm_sq_of_natDegree_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:38:59.897125+00:00
-- url     : https://prove2.me/submissions/f2a9c990-dd6a-4bc3-86ed-415d0ef18555

import Definitions.Def_Operator_Crouzeix_ProductContour
import Definitions.Def_Operator_Crouzeix_VonNeumann
import Definitions.Def_Operator_Crouzeix_ProductBase
import Theorems.Thm_polynomialSupNorm_C_of_nonempty
import Theorems.Thm_crouzeixPolynomialAuxiliaryOperator_C_eq_star_smul_one
import Theorems.Thm_mem_numericalRange
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution
    [CompleteSpace E] (A : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (p : Polynomial ℂ) {K : Set ℂ} (hK : K.Nonempty) (hp : p.natDegree = 0)
    (hCauchy : contourIntegral (resolvent A) Omega.boundaryParam =
      (2 * (Real.pi : ℂ) * Complex.I) • (1 : E →L[ℂ] E)) :
    ‖Polynomial.aeval A p * crouzeixPolynomialAuxiliaryOperator A Omega p‖ ≤
      polynomialSupNorm p K ^ 2 := by
  rw [Polynomial.eq_C_of_natDegree_eq_zero hp]
  let a := p.coeff 0
  rw [crouzeixPolynomialAuxiliaryOperator_C_eq_star_smul_one A Omega a hCauchy]
  rcases subsingleton_or_nontrivial E with hE | hE
  · let _ := hE
    have hzero : Polynomial.aeval A (Polynomial.C a) *
        (star a • (1 : E →L[ℂ] E)) = 0 := Subsingleton.elim _ _
    rw [hzero, norm_zero]
    exact sq_nonneg _
  · let _ := hE
    rw [Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one]
    simp only [smul_mul_smul, norm_smul, norm_mul, norm_star, norm_one, mul_one]
    rw [polynomialSupNorm_C_of_nonempty a hK]
    change ‖a‖ * ‖a‖ ≤ ‖a‖ ^ 2
    rw [pow_two]
