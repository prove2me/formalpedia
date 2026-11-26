-- Prove2me | solution 1 for contourIntegral_inv_sub_mul_eq_contourIntegral_inv_sub_mul_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:28:24.657265+00:00
-- url     : https://prove2.me/submissions/66c7f838-908d-4c7a-b8f6-11dcf4b23b6a

import Definitions.Def_Operator_Crouzeix_SmoothJordanCauchy
import Definitions.Def_Operator_Crouzeix_ScalarCauchyKernelWinding
import Mathlib.Analysis.Complex.RemovableSingularity
import Definitions.Def_Operator_Crouzeix_SmoothJordanCauchyFormula
import Theorems.Thm_DiffContOnCl_dslope_of_mem_isOpen
import Theorems.Thm_ContourIntegrable_of_continuousOn
import Theorems.Thm_SmoothJordanDomain_canonicalOrientation_carrier
import Theorems.Thm_SmoothJordanDomain_reverseOrientation_boundaryParam
import Theorems.Thm_SmoothJordanDomain_reverseOrientation_carrier
import Theorems.Thm_contourIntegral_eq_zero_of_diffContOnCl_smoothJordan
import Theorems.Thm_contourIntegral_mul_const
import Theorems.Thm_contourIntegral_sub
import Theorems.Thm_crouzeixPolynomialScalarCompanionBoundaryValue_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionDeriv_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanion_zero
import Theorems.Thm_mem_numericalRange
attribute [local simp] SmoothJordanDomain.canonicalOrientation_carrier
attribute [local simp] SmoothJordanDomain.reverseOrientation_boundaryParam
attribute [local simp] SmoothJordanDomain.reverseOrientation_carrier
attribute [local simp] crouzeixPolynomialScalarCompanionBoundaryValue_zero
attribute [local simp] crouzeixPolynomialScalarCompanionDeriv_zero
attribute [local simp] crouzeixPolynomialScalarCompanionRegularized_zero
attribute [local simp] crouzeixPolynomialScalarCompanion_zero
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Topology
theorem _root_.solution
    (Omega : SmoothJordanDomain) {f : ℂ → ℂ}
    (hf : DiffContOnCl ℂ f Omega.carrier) {z : ℂ}
    (hz : z ∈ Omega.carrier) :
    contourIntegral (fun sigma => (sigma - z)⁻¹ * f sigma)
        Omega.boundaryParam =
      contourIntegral (fun sigma : ℂ => (sigma - z)⁻¹)
        Omega.boundaryParam * f z := by
  have hfrontier (t : ℝ) :
      Omega.boundaryParam t ∈ frontier Omega.carrier := by
    rw [← Omega.boundaryParam_range]
    exact mem_range_self t
  have hne (t : ℝ) : Omega.boundaryParam t ≠ z := by
    intro heq
    have hzfrontier : z ∈ frontier Omega.carrier := by
      rw [← heq]
      exact hfrontier t
    have : z ∈ (∅ : Set ℂ) := by
      rw [← Omega.isOpen_carrier.inter_frontier_eq]
      exact ⟨hz, hzfrontier⟩
    exact this
  have htrace : Omega.boundaryParam '' Icc (0 : ℝ) (2 * Real.pi) ⊆
      closure Omega.carrier := by
    rintro _ ⟨t, _ht, rfl⟩
    exact frontier_subset_closure (hfrontier t)
  have htrace_ne : ∀ sigma ∈
      Omega.boundaryParam '' Icc (0 : ℝ) (2 * Real.pi), sigma - z ≠ 0 := by
    rintro _ ⟨t, _ht, rfl⟩
    exact sub_ne_zero.mpr (hne t)
  have hinv : ContourIntegrable (fun sigma : ℂ => (sigma - z)⁻¹)
      Omega.boundaryParam := by
    apply ContourIntegrable.of_continuousOn
    · exact Omega.boundaryParam_contDiff.continuous.continuousOn
    · exact
        (Omega.boundaryParam_contDiff.continuous_deriv
          (by norm_num)).continuousOn
    · exact ((continuous_id.sub continuous_const).continuousOn.inv₀ htrace_ne)
  have hinvf : ContourIntegrable (fun sigma : ℂ => (sigma - z)⁻¹ * f sigma)
      Omega.boundaryParam := by
    apply ContourIntegrable.of_continuousOn
    · exact Omega.boundaryParam_contDiff.continuous.continuousOn
    · exact
        (Omega.boundaryParam_contDiff.continuous_deriv
          (by norm_num)).continuousOn
    · exact ((continuous_id.sub continuous_const).continuousOn.inv₀ htrace_ne).mul
        (hf.continuousOn.mono htrace)
  have hinvconst : ContourIntegrable
      (fun sigma : ℂ => (sigma - z)⁻¹ * f z) Omega.boundaryParam := by
    apply ContourIntegrable.of_continuousOn
    · exact Omega.boundaryParam_contDiff.continuous.continuousOn
    · exact
        (Omega.boundaryParam_contDiff.continuous_deriv
          (by norm_num)).continuousOn
    · exact ((continuous_id.sub continuous_const).continuousOn.inv₀ htrace_ne).mul
        continuousOn_const
  have hzero := contourIntegral_eq_zero_of_diffContOnCl_smoothJordan
    Omega (hf.dslope_of_mem_isOpen Omega.isOpen_carrier hz)
  have hrewrite : contourIntegral (dslope f z) Omega.boundaryParam =
      contourIntegral
        (fun sigma : ℂ =>
          (sigma - z)⁻¹ * f sigma - (sigma - z)⁻¹ * f z)
        Omega.boundaryParam := by
    unfold contourIntegral
    apply intervalIntegral.integral_congr
    intro t _ht
    change deriv Omega.boundaryParam t * dslope f z (Omega.boundaryParam t) =
      deriv Omega.boundaryParam t *
        ((Omega.boundaryParam t - z)⁻¹ * f (Omega.boundaryParam t) -
          (Omega.boundaryParam t - z)⁻¹ * f z)
    rw [dslope_of_ne f (hne t)]
    simp only [slope_def_module, smul_eq_mul]
    ring
  rw [hrewrite, contourIntegral_sub hinvf hinvconst,
    contourIntegral_mul_const (f z) hinv] at hzero
  exact sub_eq_zero.mp hzero
