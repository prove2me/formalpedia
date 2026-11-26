-- Prove2me | solution 1 for contourIntegral_inv_sub_eq_zero_of_not_mem_closure_carrier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:11:17.242708+00:00
-- url     : https://prove2.me/submissions/76802878-59db-4b47-b681-21dbccefc64c

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
    (Omega : SmoothJordanDomain) {z : ℂ}
    (hz : z ∉ closure Omega.carrier) :
    contourIntegral (fun sigma : ℂ => (sigma - z)⁻¹)
      Omega.boundaryParam = 0 := by
  have hconvex : Convex ℝ (closure Omega.carrier) :=
    Omega.strictConvex_carrier.convex.closure
  obtain ⟨f, u, hf, hfz⟩ :=
    RCLike.geometric_hahn_banach_closed_point (𝕜 := ℂ)
      hconvex isClosed_closure hz
  have hfrontier (t : ℝ) :
      Omega.boundaryParam t ∈ closure Omega.carrier :=
    frontier_subset_closure (by
      rw [← Omega.boundaryParam_range]
      exact mem_range_self t)
  have hne (t : ℝ) : Omega.boundaryParam t ≠ z := by
    intro heq
    apply hz
    rw [← heq]
    exact hfrontier t
  have hslit (t : ℝ) :
      f (z - Omega.boundaryParam t) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    left
    rw [map_sub, Complex.sub_re]
    have ht := hf (Omega.boundaryParam t) (hfrontier t)
    exact sub_pos.mpr (ht.trans hfz)
  have hfa (w : ℂ) : f w = w * f 1 := by
    simpa only [smul_eq_mul, mul_one] using
      (map_smul f w (1 : ℂ))
  have ha : f 1 ≠ 0 := by
    intro ha
    have hzero (w : ℂ) : f w = 0 := by
      rw [hfa, ha, mul_zero]
    have ht := hf (Omega.boundaryParam 0) (hfrontier 0)
    rw [hzero] at ht hfz
    simp only [map_zero] at ht hfz
    linarith
  have hslit' (t : ℝ) :
      (z - Omega.boundaryParam t) * f 1 ∈ Complex.slitPlane := by
    rw [← hfa]
    exact hslit t
  let Fp : ℂ → ℂ := fun w => Complex.log ((z - w) * f 1)
  have hF : ∀ t ∈ Icc (0 : ℝ) (2 * Real.pi),
      HasDerivAt Fp ((Omega.boundaryParam t - z)⁻¹)
        (Omega.boundaryParam t) := by
    intro t _ht
    have hsub : HasDerivAt (fun w : ℂ => z - w) (-1)
        (Omega.boundaryParam t) :=
      (hasDerivAt_id' (Omega.boundaryParam t)).const_sub z
    have hinner : HasDerivAt (fun w : ℂ => (z - w) * f 1) (-f 1)
        (Omega.boundaryParam t) := by
      simpa only [neg_mul, one_mul] using hsub.mul_const (f 1)
    have hlog' : HasDerivAt Fp
        ((-f 1) / ((z - Omega.boundaryParam t) * f 1))
        (Omega.boundaryParam t) := by
      simpa only [Fp] using hinner.clog (hslit' t)
    have hderiv :
        (-f 1) / ((z - Omega.boundaryParam t) * f 1) =
          (Omega.boundaryParam t - z)⁻¹ := by
      field_simp [ha, sub_ne_zero.mpr (hne t).symm,
        sub_ne_zero.mpr (hne t)]
      ring
    rw [hderiv] at hlog'
    exact hlog'
  apply contourIntegral_eq_zero_of_hasDerivAt_of_closed
    (Fp := Fp)
  · intro t _
    exact
      (Omega.boundaryParam_contDiff.differentiable
        (by norm_num)).differentiableAt
  · exact hF
  · apply ContourIntegrable.of_continuousOn
    · exact Omega.boundaryParam_contDiff.continuous.continuousOn
    · exact
        (Omega.boundaryParam_contDiff.continuous_deriv
          (by norm_num)).continuousOn
    · apply ContinuousOn.inv₀
      · exact (continuous_id.sub continuous_const).continuousOn
      · rintro _ ⟨t, _ht, rfl⟩
        exact sub_ne_zero.mpr (hne t)
  · simpa only [zero_add] using Omega.boundaryParam_periodic 0
