-- Prove2me | solution 1 for crouzeixPolynomialAuxiliaryOperator_C_eq_star_smul_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:37:50.065963+00:00
-- url     : https://prove2.me/submissions/8ca7ceea-16f6-470d-b33b-b62a77c831b9

import Definitions.Def_Operator_Crouzeix_ProductContour
import Definitions.Def_Operator_Crouzeix_VonNeumann
import Definitions.Def_Operator_Crouzeix_ProductBase
import Theorems.Thm_normalized_contourIntegral_resolvent_eq_one_of_cauchy
import Theorems.Thm_contourIntegral_smul
import Theorems.Thm_mem_numericalRange
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution
    [CompleteSpace E] (A : E →L[ℂ] E) (Omega : SmoothJordanDomain) (a : ℂ)
    (hCauchy : contourIntegral (resolvent A) Omega.boundaryParam =
      (2 * (Real.pi : ℂ) * Complex.I) • (1 : E →L[ℂ] E)) :
    crouzeixPolynomialAuxiliaryOperator A Omega (Polynomial.C a) =
      star a • (1 : E →L[ℂ] E) := by
  unfold crouzeixPolynomialAuxiliaryOperator crouzeixAuxiliaryOperator
  simp only [Polynomial.eval_C]
  rw [contourIntegral_smul, smul_smul]
  rw [mul_comm (2 * (Real.pi : ℂ) * Complex.I)⁻¹ (star a), ← smul_smul]
  rw [normalized_contourIntegral_resolvent_eq_one_of_cauchy A Omega hCauchy]
