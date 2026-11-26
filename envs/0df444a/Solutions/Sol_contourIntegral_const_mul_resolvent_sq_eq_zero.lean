-- Prove2me | solution 1 for contourIntegral_const_mul_resolvent_sq_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:11:30.122265+00:00
-- url     : https://prove2.me/submissions/67ab5813-75fe-4eb8-a2bb-0e7467b55f25

import Definitions.Def_Operator_Crouzeix_ScalarCauchyKernelWinding
import Definitions.Def_Operator_SpectralSet_SpectrumInNR
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Definitions.Def_Operator_Crouzeix_ResolventContourHomotopy
import Theorems.Thm_ContourIntegrable_of_continuousOn
import Theorems.Thm_SmoothJordanDomain_canonicalOrientation_carrier
import Theorems.Thm_SmoothJordanDomain_reverseOrientation_boundaryParam
import Theorems.Thm_SmoothJordanDomain_reverseOrientation_carrier
import Theorems.Thm_contourIntegral_eq_zero_of_hasDerivAt_of_closed
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
    (hres : ∀ t : ℝ,
      Omega.boundaryParam t ∈ resolventSet ℂ B) :
    contourIntegral (fun z : ℂ => D * resolvent B z ^ 2)
      Omega.boundaryParam = 0 := by
  have hint : ContourIntegrable
      (fun z : ℂ => D * resolvent B z ^ 2) Omega.boundaryParam := by
    apply ContourIntegrable.of_continuousOn
    · exact Omega.boundaryParam_contDiff.continuous.continuousOn
    · exact
        (Omega.boundaryParam_contDiff.continuous_deriv
          (by norm_num)).continuousOn
    · intro z hz
      obtain ⟨t, _, rfl⟩ := hz
      exact (continuousAt_const.mul
        ((spectrum.hasDerivAt_resolvent_const_left
          (hres t)).continuousAt.pow 2)).continuousWithinAt
  apply contourIntegral_eq_zero_of_hasDerivAt_of_closed
    (Fp := fun z : ℂ => -(D * resolvent B z))
  · intro _ _
    exact
      (Omega.boundaryParam_contDiff.differentiable (by norm_num)).differentiableAt
  · intro t _
    have hder :=
      ((spectrum.hasDerivAt_resolvent_const_left (hres t)).const_mul D).neg
    convert hder using 1
    · rfl
    · simp only [mul_neg, neg_neg]
  · exact hint
  · simpa only [zero_add] using Omega.boundaryParam_periodic 0
