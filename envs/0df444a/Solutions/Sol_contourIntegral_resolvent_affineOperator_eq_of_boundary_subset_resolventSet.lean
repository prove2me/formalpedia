-- Prove2me | solution 1 for contourIntegral_resolvent_affineOperator_eq_of_boundary_subset_resolventSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:31:52.165902+00:00
-- url     : https://prove2.me/submissions/ad0bdac4-be79-4548-b599-33cd55cd35ca

import Definitions.Def_Operator_Crouzeix_ScalarCauchyKernelWinding
import Definitions.Def_Operator_SpectralSet_SpectrumInNR
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Definitions.Def_Operator_Crouzeix_ResolventContourHomotopy
import Theorems.Thm_hasDerivAt_contourIntegral_resolvent_affineOperator_eq_zero
import Theorems.Thm_SmoothJordanDomain_canonicalOrientation_carrier
import Theorems.Thm_SmoothJordanDomain_reverseOrientation_boundaryParam
import Theorems.Thm_SmoothJordanDomain_reverseOrientation_carrier
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
open Complex Filter MeasureTheory Metric Set spectrum
open scoped InnerProductSpace Interval Pointwise Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (B D : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (hBD : Commute B D)
    (hres : ∀ r ∈ Icc (0 : ℝ) 1, ∀ t : ℝ,
      Omega.boundaryParam t ∈
        resolventSet ℂ (B + (r : ℂ) • D)) :
    contourIntegral (resolvent (B + D)) Omega.boundaryParam =
      contourIntegral (resolvent B) Omega.boundaryParam := by
  let M : ℝ → (E →L[ℂ] E) := fun r =>
    contourIntegral (resolvent (B + (r : ℂ) • D)) Omega.boundaryParam
  have hderiv : ∀ r ∈ uIcc (0 : ℝ) 1, HasDerivAt M 0 r := by
    intro r hr
    rw [uIcc_of_le zero_le_one] at hr
    simpa only [M, Function.comp_apply, Complex.ofRealCLM_apply, smul_zero] using!
      (hasDerivAt_contourIntegral_resolvent_affineOperator_eq_zero
        B D Omega (r : ℂ) hBD (hres r hr)).scomp r
          Complex.ofRealCLM.hasDerivAt
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := M) (f' := fun _ : ℝ => (0 : E →L[ℂ] E)) hderiv
    (continuous_const.intervalIntegrable (0 : ℝ) 1)
  have hM : M 1 = M 0 := by
    rw [intervalIntegral.integral_zero] at hftc
    exact sub_eq_zero.mp hftc.symm
  simpa only [M, Complex.ofReal_one, one_smul, Complex.ofReal_zero,
    zero_smul, add_zero] using hM
