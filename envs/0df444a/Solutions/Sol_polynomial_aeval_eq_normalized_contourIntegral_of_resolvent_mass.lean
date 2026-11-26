-- Prove2me | solution 1 for polynomial_aeval_eq_normalized_contourIntegral_of_resolvent_mass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:38:10.57932+00:00
-- url     : https://prove2.me/submissions/466ae3f4-1f9b-4748-b5ca-4b2630d0fce6

import Definitions.Def_Operator_Crouzeix_ProductContour
import Definitions.Def_Operator_Crouzeix_PolynomialCauchyFromResolventMass
import Theorems.Thm_contourIntegral_aeval_divByMonic_X_sub_C_eq_zero
import Theorems.Thm_ContourIntegrable_of_continuousOn
import Theorems.Thm_SmoothJordanDomain_boundaryParam_mem_resolventSet
import Theorems.Thm_aeval_mul_resolvent_eq_eval_mul_resolvent_sub_aeval_divByMonic
import Theorems.Thm_continuous_aeval_divByMonic_X_sub_C
import Theorems.Thm_contourIntegral_add
import Theorems.Thm_contourIntegral_const_mul
import Theorems.Thm_crouzeixAuxiliaryIntegrand_contourIntegrable
import Theorems.Thm_mem_numericalRange
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier)
    (hmass : contourIntegral (resolvent A) Omega.boundaryParam =
      (2 * (Real.pi : ℂ) * I) • (1 : E →L[ℂ] E))
    (p : Polynomial ℂ) :
    Polynomial.aeval A p =
      (2 * (Real.pi : ℂ) * I)⁻¹ •
        contourIntegral
          (fun z => Polynomial.eval z p • resolvent A z)
          Omega.boundaryParam := by
  let F : E →L[ℂ] E := Polynomial.aeval A p
  let Q : ℂ → E →L[ℂ] E := fun z =>
    Polynomial.aeval A (p /ₘ (Polynomial.X - Polynomial.C z))
  have hresolvent : ContourIntegrable (resolvent A) Omega.boundaryParam := by
    simpa only [one_smul] using
      crouzeixAuxiliaryIntegrand_contourIntegrable A Omega (fun _ => 1)
        hOmega continuous_const.continuousOn
  have hQ : ContourIntegrable Q Omega.boundaryParam := by
    apply ContourIntegrable.of_continuousOn
    · exact Omega.boundaryParam_contDiff.continuous.continuousOn
    · exact
        (Omega.boundaryParam_contDiff.continuous_deriv (by norm_num)).continuousOn
    · exact (continuous_aeval_divByMonic_X_sub_C A p).continuousOn
  have hFresolvent : ContourIntegrable (fun z => F * resolvent A z)
      Omega.boundaryParam := by
    unfold ContourIntegrable at hresolvent ⊢
    have hfun :
        (fun t => deriv Omega.boundaryParam t •
          (F * resolvent A (Omega.boundaryParam t))) =
        fun t => F * (deriv Omega.boundaryParam t •
          resolvent A (Omega.boundaryParam t)) := by
      funext t
      exact (Algebra.mul_smul_comm (deriv Omega.boundaryParam t) F
        (resolvent A (Omega.boundaryParam t))).symm
    rw [hfun]
    exact hresolvent.const_mul F
  have hpoint : ∀ t : ℝ,
      Polynomial.eval (Omega.boundaryParam t) p •
          resolvent A (Omega.boundaryParam t) =
        F * resolvent A (Omega.boundaryParam t) +
          Q (Omega.boundaryParam t) := by
    intro t
    have h := aeval_mul_resolvent_eq_eval_mul_resolvent_sub_aeval_divByMonic
      A p (Omega.boundaryParam_mem_resolventSet A hOmega t)
    dsimp only [F, Q]
    exact ((eq_sub_iff_add_eq).mp h).symm
  have hsplit :
      contourIntegral (fun z => Polynomial.eval z p • resolvent A z)
          Omega.boundaryParam =
        contourIntegral (fun z => F * resolvent A z) Omega.boundaryParam +
          contourIntegral Q Omega.boundaryParam := by
    rw [← contourIntegral_add hFresolvent hQ]
    unfold contourIntegral
    apply intervalIntegral.integral_congr
    intro t _
    exact congrArg (fun T : E →L[ℂ] E =>
      deriv Omega.boundaryParam t • T) (hpoint t)
  rw [hsplit, contourIntegral_const_mul F hresolvent]
  have hQzero : contourIntegral Q Omega.boundaryParam = 0 := by
    exact contourIntegral_aeval_divByMonic_X_sub_C_eq_zero A Omega p
  rw [hQzero, add_zero, hmass]
  dsimp only [F]
  simp only [mul_smul_comm, mul_one, smul_smul]
  rw [inv_mul_cancel₀]
  · exact (one_smul ℂ (Polynomial.aeval A p)).symm
  · exact mul_ne_zero (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
