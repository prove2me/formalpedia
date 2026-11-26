-- Prove2me | solution 1 for normalized_contourIntegral_inv_sub_smul_resolvent_eq_resolvent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:41:51.248555+00:00
-- url     : https://prove2.me/submissions/1027512b-c280-479e-a54e-c87b11d74dd6

import Definitions.Def_Operator_Crouzeix_ScalarCauchyKernelConstancy
import Definitions.Def_Operator_Crouzeix_CircleCauchy
import Definitions.Def_Operator_Crouzeix_ResolventCauchyKernel
import Theorems.Thm_contourIntegral_inv_sub_smul_resolvent_eq_two_pi_I_smul_resolvent

set_option autoImplicit false
open Complex Set spectrum
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain) (sigma : ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier)
    (hmass : contourIntegral (resolvent A) Omega.boundaryParam =
      (2 * (Real.pi : ℂ) * I) • (1 : E →L[ℂ] E))
    (hsigma : sigma ∉ closure Omega.carrier) :
    (2 * (Real.pi : ℂ) * I)⁻¹ •
        contourIntegral (fun z => (sigma - z)⁻¹ • resolvent A z)
          Omega.boundaryParam =
      resolvent A sigma := by
  rw [contourIntegral_inv_sub_smul_resolvent_eq_two_pi_I_smul_resolvent
    A Omega sigma hOmega hmass hsigma, smul_smul,
    inv_mul_cancel₀]
  · exact one_smul ℂ (resolvent A sigma)
  · exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr
      Real.pi_ne_zero)) Complex.I_ne_zero
