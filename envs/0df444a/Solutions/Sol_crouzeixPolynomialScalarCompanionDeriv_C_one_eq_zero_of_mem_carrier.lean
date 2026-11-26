-- Prove2me | solution 1 for crouzeixPolynomialScalarCompanionDeriv_C_one_eq_zero_of_mem_carrier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:28:21.281012+00:00
-- url     : https://prove2.me/submissions/4b1bd7cd-ffeb-49d7-bbe0-4fc6918927a3

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Definitions.Def_Operator_Crouzeix_ScalarCauchyKernelConstancy
import Theorems.Thm_ContourIntegrable_of_continuousOn
import Theorems.Thm_contourIntegral_eq_zero_of_hasDerivAt_of_closed
import Theorems.Thm_crouzeixPolynomialScalarCompanionBoundaryValue_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionDeriv_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanion_zero
import Theorems.Thm_mem_numericalRange
attribute [local simp] crouzeixPolynomialScalarCompanionBoundaryValue_zero
attribute [local simp] crouzeixPolynomialScalarCompanionDeriv_zero
attribute [local simp] crouzeixPolynomialScalarCompanionRegularized_zero
attribute [local simp] crouzeixPolynomialScalarCompanion_zero
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open Complex Set
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) {z : ℂ} (hz : z ∈ Omega.carrier) :
    crouzeixPolynomialScalarCompanionDeriv Omega (Polynomial.C 1) z = 0 := by
  have hne : ∀ t : ℝ, Omega.boundaryParam t - z ≠ 0 := by
    intro t hzero
    have heq : Omega.boundaryParam t = z := sub_eq_zero.mp hzero
    have hfrontier : z ∈ frontier Omega.carrier := by
      rw [← heq, ← Omega.boundaryParam_range]
      exact mem_range_self t
    have hempty : z ∈ (∅ : Set ℂ) := by
      rw [← Omega.isOpen_carrier.inter_frontier_eq]
      exact ⟨hz, hfrontier⟩
    exact hempty
  have hzero : contourIntegral (fun sigma : ℂ => (sigma - z)⁻¹ ^ 2)
      Omega.boundaryParam = 0 := by
    apply contourIntegral_eq_zero_of_hasDerivAt_of_closed
      (Fp := fun sigma : ℂ => -(sigma - z)⁻¹)
    · intro _ _
      exact
        (Omega.boundaryParam_contDiff.differentiable (by norm_num)).differentiableAt
    · intro t _
      have hsub : HasDerivAt (fun sigma : ℂ => sigma - z) 1
          (Omega.boundaryParam t) := (hasDerivAt_id _).sub_const z
      have hinv := hsub.inv (hne t)
      convert hinv.neg using 1
      · rfl
      · rw [inv_pow]
        ring
    · apply ContourIntegrable.of_continuousOn
      · exact Omega.boundaryParam_contDiff.continuous.continuousOn
      · exact
          (Omega.boundaryParam_contDiff.continuous_deriv (by norm_num)).continuousOn
      · apply ContinuousOn.pow
        apply ContinuousOn.inv₀
        · exact (continuous_id.sub continuous_const).continuousOn
        · rintro _ ⟨t, _, rfl⟩
          exact hne t
    · simpa only [zero_add] using Omega.boundaryParam_periodic 0
  unfold contourIntegral at hzero
  unfold crouzeixPolynomialScalarCompanionDeriv
  simp only [Polynomial.eval_C, star_one, mul_one, smul_eq_mul] at hzero ⊢
  rw [hzero, mul_zero]
