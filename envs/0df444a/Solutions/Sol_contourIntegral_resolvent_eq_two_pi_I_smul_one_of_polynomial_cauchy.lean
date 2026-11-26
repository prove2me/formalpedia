-- Prove2me | solution 1 for contourIntegral_resolvent_eq_two_pi_I_smul_one_of_polynomial_cauchy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:51:37.486515+00:00
-- url     : https://prove2.me/submissions/81dc2a7d-bbeb-4e26-a22a-1753cde892b7

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Definitions.Def_Operator_Crouzeix_PolynomialCauchyMass
import Theorems.Thm_mem_numericalRange
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open Complex
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (hCauchyP : ∀ p : Polynomial ℂ,
      Polynomial.aeval A p =
        (2 * (Real.pi : ℂ) * I)⁻¹ •
          contourIntegral
            (fun z => Polynomial.eval z p • resolvent A z)
            Omega.boundaryParam) :
    contourIntegral (resolvent A) Omega.boundaryParam =
      (2 * (Real.pi : ℂ) * I) • (1 : E →L[ℂ] E) := by
  let c : ℂ := 2 * (Real.pi : ℂ) * I
  have hc : c ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  have h := hCauchyP (Polynomial.C 1)
  simp only [Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one,
    Polynomial.eval_C, one_smul] at h
  change (1 : E →L[ℂ] E) =
    c⁻¹ • contourIntegral (resolvent A) Omega.boundaryParam at h
  change contourIntegral (resolvent A) Omega.boundaryParam =
    c • (1 : E →L[ℂ] E)
  calc
    contourIntegral (resolvent A) Omega.boundaryParam =
        (1 : ℂ) • contourIntegral (resolvent A) Omega.boundaryParam := by
      exact (one_smul ℂ _).symm
    _ = (c * c⁻¹) • contourIntegral (resolvent A) Omega.boundaryParam := by
      rw [mul_inv_cancel₀ hc]
    _ = c • (c⁻¹ • contourIntegral (resolvent A) Omega.boundaryParam) := by
      rw [smul_smul]
    _ = c • (1 : E →L[ℂ] E) := by rw [← h]
