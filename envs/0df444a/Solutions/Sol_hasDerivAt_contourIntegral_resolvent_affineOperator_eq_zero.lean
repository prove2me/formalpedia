-- Prove2me | solution 1 for hasDerivAt_contourIntegral_resolvent_affineOperator_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:31:04.483646+00:00
-- url     : https://prove2.me/submissions/39912f1d-a5e2-49b7-81a2-8c9be7a37dd6

import Definitions.Def_Operator_Crouzeix_ScalarCauchyKernelWinding
import Definitions.Def_Operator_SpectralSet_SpectrumInNR
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Definitions.Def_Operator_Crouzeix_ResolventContourHomotopy
import Theorems.Thm_hasDerivAt_contourIntegral_resolvent_affineOperator_of_boundary_subset_resolventSet
import Theorems.Thm_commute_resolvent_of_commute
import Theorems.Thm_contourIntegral_const_mul_resolvent_sq_eq_zero
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
    (B D : E →L[ℂ] E) (Omega : SmoothJordanDomain) (s : ℂ)
    (hBD : Commute B D)
    (hres : ∀ t : ℝ,
      Omega.boundaryParam t ∈ resolventSet ℂ (B + s • D)) :
    HasDerivAt
      (fun w : ℂ =>
        contourIntegral (resolvent (B + w • D)) Omega.boundaryParam)
      0 s := by
  have hraw :=
    hasDerivAt_contourIntegral_resolvent_affineOperator_of_boundary_subset_resolventSet
      B D Omega s hres
  convert hraw using 1
  have hzero := contourIntegral_const_mul_resolvent_sq_eq_zero
    (B + s • D) D Omega hres
  rw [← hzero]
  simp only [contourIntegral]
  apply intervalIntegral.integral_congr
  intro t _ht
  apply congrArg (fun R : E →L[ℂ] E => deriv Omega.boundaryParam t • R)
  let R := resolvent (B + s • D) (Omega.boundaryParam t)
  have hDBs : Commute D (B + s • D) :=
    hBD.symm.add_right ((Commute.refl D).smul_right s)
  have hcomm : Commute D R :=
    commute_resolvent_of_commute (B + s • D) D
      (Omega.boundaryParam t) hDBs (hres t)
  simpa only [R, pow_two, mul_assoc] using
    congrArg (fun X : E →L[ℂ] E => X * R) hcomm.eq
