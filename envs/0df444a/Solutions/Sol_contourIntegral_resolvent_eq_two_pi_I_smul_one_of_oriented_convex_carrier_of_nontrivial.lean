-- Prove2me | solution 1 for contourIntegral_resolvent_eq_two_pi_I_smul_one_of_oriented_convex_carrier_of_nontrivial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:33:43.331202+00:00
-- url     : https://prove2.me/submissions/a0790f96-4788-48be-8055-b47cab50524f

import Definitions.Def_Operator_Crouzeix_ScalarCauchyKernelWinding
import Definitions.Def_Operator_SpectralSet_SpectrumInNR
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Definitions.Def_Operator_Crouzeix_ResolventContourHomotopy
import Theorems.Thm_contourIntegral_resolvent_eq_scalar_of_convex_carrier
import Theorems.Thm_contourIntegral_resolvent_smul_one_eq_scalar
import Theorems.Thm_SmoothJordanDomain_canonicalOrientation_carrier
import Theorems.Thm_SmoothJordanDomain_reverseOrientation_boundaryParam
import Theorems.Thm_SmoothJordanDomain_reverseOrientation_carrier
import Theorems.Thm_crouzeixPolynomialScalarCompanionBoundaryValue_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionDeriv_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanion_zero
import Theorems.Thm_crouzeixScalarCauchyKernel_eq_one_of_oriented_carrier_point
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
open Complex Filter MeasureTheory Metric Set spectrum
open scoped InnerProductSpace Interval Pointwise Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    [Nontrivial E] (A : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (c : ℂ) (hc : c ∈ Omega.carrier)
    (hcside : ∀ t : ℝ,
      ((starRingEnd ℂ) (-I * deriv Omega.boundaryParam t) *
        (c - Omega.boundaryParam t)).re ≤ 0)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier) :
    contourIntegral (resolvent A) Omega.boundaryParam =
      (2 * (Real.pi : ℂ) * I) • (1 : E →L[ℂ] E) := by
  rw [contourIntegral_resolvent_eq_scalar_of_convex_carrier
    A Omega c hc hOmega,
    contourIntegral_resolvent_smul_one_eq_scalar Omega c hc]
  have hkernel :=
    crouzeixScalarCauchyKernel_eq_one_of_oriented_carrier_point
      Omega c hc hcside
  unfold crouzeixScalarCauchyKernel at hkernel
  let q : ℂ := 2 * (Real.pi : ℂ) * I
  have hq : q ≠ 0 := by
    dsimp only [q]
    exact mul_ne_zero (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  have hkernel' : q⁻¹ * contourIntegral (fun z : ℂ => (z - c)⁻¹)
      Omega.boundaryParam = 1 := by
    simpa only [q] using hkernel
  have hscaled := congrArg (fun z : ℂ => q * z) hkernel'
  have hscalar : contourIntegral (fun z : ℂ => (z - c)⁻¹)
      Omega.boundaryParam = q := by
    calc
      contourIntegral (fun z : ℂ => (z - c)⁻¹) Omega.boundaryParam =
          (q * q⁻¹) * contourIntegral (fun z : ℂ => (z - c)⁻¹)
            Omega.boundaryParam := by rw [mul_inv_cancel₀ hq, one_mul]
      _ = q * (q⁻¹ * contourIntegral (fun z : ℂ => (z - c)⁻¹)
            Omega.boundaryParam) := by rw [mul_assoc]
      _ = q * 1 := hscaled
      _ = q := mul_one q
  rw [hscalar]
