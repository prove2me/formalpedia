-- Prove2me | solution 1 for norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_le_main_add_remainder
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:19:56.673063+00:00
-- url     : https://prove2.me/submissions/af6ecb3e-a22d-498c-b185-187e033dda4e

import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Mathlib.Topology.Algebra.Polynomial
import Definitions.Def_Operator_Crouzeix_ProductContour
import Theorems.Thm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_eq_main_sub_remainder

set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution
    [CompleteSpace E] (A : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (p : Polynomial ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier) :
    ‖Polynomial.aeval A p * crouzeixPolynomialAuxiliaryOperator A Omega p‖ ≤
      ‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
        contourIntegral
          (fun z => (star (Polynomial.eval z p) * Polynomial.eval z p) •
            resolvent A z) Omega.boundaryParam‖ +
      ‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
        contourIntegral
          (fun z => star (Polynomial.eval z p) •
            Polynomial.aeval A (p /ₘ (Polynomial.X - Polynomial.C z)))
          Omega.boundaryParam‖ := by
  rw [aeval_mul_crouzeixPolynomialAuxiliaryOperator_eq_main_sub_remainder
    A Omega p hOmega]
  exact norm_sub_le _ _
