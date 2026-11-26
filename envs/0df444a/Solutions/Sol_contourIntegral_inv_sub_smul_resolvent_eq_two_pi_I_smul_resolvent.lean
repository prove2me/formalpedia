-- Prove2me | solution 1 for contourIntegral_inv_sub_smul_resolvent_eq_two_pi_I_smul_resolvent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:39:04.156295+00:00
-- url     : https://prove2.me/submissions/09816ecb-8c50-48fb-8a64-4e7d7f3a5cfe

import Definitions.Def_Operator_Crouzeix_ScalarCauchyKernelConstancy
import Definitions.Def_Operator_Crouzeix_CircleCauchy
import Definitions.Def_Operator_Crouzeix_ResolventCauchyKernel
import Theorems.Thm_inv_sub_smul_resolvent_eq_resolvent_mul_resolvent_add
import Theorems.Thm_contourIntegral_smul_const
import Theorems.Thm_ContourIntegrable_of_continuousOn
import Theorems.Thm_SmoothJordanDomain_boundaryParam_mem_resolventSet
import Theorems.Thm_contourIntegral_add
import Theorems.Thm_contourIntegral_inv_sub_eq_zero_of_not_mem_closure_carrier
import Theorems.Thm_contourIntegral_mul_const
import Theorems.Thm_contourIntegral_neg
import Theorems.Thm_spectrum_subset_closure_numericalRange


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
    contourIntegral (fun z => (sigma - z)⁻¹ • resolvent A z)
        Omega.boundaryParam =
      (2 * (Real.pi : ℂ) * I) • resolvent A sigma := by
  have hsigmaR : sigma ∈ resolventSet ℂ A := by
    by_contra hrho
    have hspectrum : sigma ∈ spectrum ℂ A := hrho
    exact hsigma (subset_closure
      (hOmega (spectrum_subset_closure_numericalRange A hspectrum)))
  have hboundaryR : ∀ t : ℝ,
      Omega.boundaryParam t ∈ resolventSet ℂ A :=
    fun t => Omega.boundaryParam_mem_resolventSet A hOmega t
  have hboundaryNe : ∀ t : ℝ, Omega.boundaryParam t ≠ sigma := by
    intro t heq
    apply hsigma
    rw [← heq]
    apply frontier_subset_closure
    rw [← Omega.boundaryParam_range]
    exact mem_range_self t
  have hres : ContourIntegrable (resolvent A) Omega.boundaryParam := by
    apply ContourIntegrable.of_continuousOn
    · exact Omega.boundaryParam_contDiff.continuous.continuousOn
    · exact
        (Omega.boundaryParam_contDiff.continuous_deriv
          (by norm_num)).continuousOn
    · rintro z ⟨t, _ht, rfl⟩
      exact (spectrum.hasDerivAt_resolvent_const_left
        (hboundaryR t)).continuousAt.continuousWithinAt
  have hresMul : ContourIntegrable
      (fun z => resolvent A z * resolvent A sigma)
      Omega.boundaryParam := by
    apply ContourIntegrable.of_continuousOn
    · exact Omega.boundaryParam_contDiff.continuous.continuousOn
    · exact
        (Omega.boundaryParam_contDiff.continuous_deriv
          (by norm_num)).continuousOn
    · apply ContinuousOn.mul
      · rintro z ⟨t, _ht, rfl⟩
        exact (spectrum.hasDerivAt_resolvent_const_left
          (hboundaryR t)).continuousAt.continuousWithinAt
      · exact continuousOn_const
  have hinvMul : ContourIntegrable
      (fun z => (sigma - z)⁻¹ • resolvent A sigma)
      Omega.boundaryParam := by
    apply ContourIntegrable.of_continuousOn
    · exact Omega.boundaryParam_contDiff.continuous.continuousOn
    · exact
        (Omega.boundaryParam_contDiff.continuous_deriv
          (by norm_num)).continuousOn
    · have hinv : ContinuousOn (fun z : ℂ => (sigma - z)⁻¹)
          (Omega.boundaryParam '' Icc (0 : ℝ) (2 * Real.pi)) := by
        apply ContinuousOn.inv₀
        · exact (continuous_const.sub continuous_id).continuousOn
        · rintro _ ⟨t, _ht, rfl⟩
          exact sub_ne_zero.mpr (hboundaryNe t).symm
      let L : ℂ →L[ℂ] (E →L[ℂ] E) :=
        (1 : ℂ →L[ℂ] ℂ).smulRight (resolvent A sigma)
      have hL : Continuous (fun a : ℂ => a • resolvent A sigma) := by
        change Continuous (L : ℂ → E →L[ℂ] E)
        exact L.continuous
      exact hL.comp_continuousOn hinv
  have hinvzero :
      contourIntegral (fun z => (sigma - z)⁻¹) Omega.boundaryParam = 0 := by
    calc
      contourIntegral (fun z => (sigma - z)⁻¹) Omega.boundaryParam =
          contourIntegral (fun z => -(z - sigma)⁻¹) Omega.boundaryParam := by
        congr 1
        funext z
        rw [show sigma - z = -(z - sigma) by ring, inv_neg]
      _ = -contourIntegral (fun z => (z - sigma)⁻¹)
          Omega.boundaryParam := contourIntegral_neg _ _
      _ = 0 := by
        rw [contourIntegral_inv_sub_eq_zero_of_not_mem_closure_carrier
          Omega hsigma, neg_zero]
  calc
    contourIntegral (fun z => (sigma - z)⁻¹ • resolvent A z)
        Omega.boundaryParam =
        contourIntegral (fun z =>
          resolvent A z * resolvent A sigma +
            (sigma - z)⁻¹ • resolvent A sigma)
          Omega.boundaryParam := by
      unfold contourIntegral
      apply intervalIntegral.integral_congr
      intro t _ht
      change deriv Omega.boundaryParam t •
          ((sigma - Omega.boundaryParam t)⁻¹ •
            resolvent A (Omega.boundaryParam t)) =
        deriv Omega.boundaryParam t •
          (resolvent A (Omega.boundaryParam t) * resolvent A sigma +
            (sigma - Omega.boundaryParam t)⁻¹ • resolvent A sigma)
      rw [inv_sub_smul_resolvent_eq_resolvent_mul_resolvent_add A (hboundaryR t)
        hsigmaR (hboundaryNe t)]
    _ = contourIntegral (fun z => resolvent A z * resolvent A sigma)
          Omega.boundaryParam +
        contourIntegral (fun z => (sigma - z)⁻¹ • resolvent A sigma)
          Omega.boundaryParam := contourIntegral_add hresMul hinvMul
    _ = contourIntegral (resolvent A) Omega.boundaryParam *
          resolvent A sigma +
        contourIntegral (fun z => (sigma - z)⁻¹) Omega.boundaryParam •
          resolvent A sigma := by
      rw [contourIntegral_mul_const (resolvent A sigma) hres,
        contourIntegral_smul_const]
    _ = (2 * (Real.pi : ℂ) * I) • resolvent A sigma := by
      rw [hmass, hinvzero,
        zero_smul, add_zero, smul_mul_assoc, one_mul]
