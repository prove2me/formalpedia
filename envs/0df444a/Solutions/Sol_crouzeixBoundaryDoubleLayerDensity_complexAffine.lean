-- Prove2me | solution 1 for crouzeixBoundaryDoubleLayerDensity_complexAffine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:46:19.250799+00:00
-- url     : https://prove2.me/submissions/7d2f042f-6af7-447c-ab6d-e3085c6bf339

import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasure
import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasureAffine
import Theorems.Thm_crouzeixPolynomialBoundaryPhaseTransform_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionBoundaryValue_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionDeriv_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanion_zero
import Theorems.Thm_mem_numericalRange
attribute [local simp] crouzeixPolynomialBoundaryPhaseTransform_zero
attribute [local simp] crouzeixPolynomialScalarCompanionBoundaryValue_zero
attribute [local simp] crouzeixPolynomialScalarCompanionDeriv_zero
attribute [local simp] crouzeixPolynomialScalarCompanionRegularized_zero
attribute [local simp] crouzeixPolynomialScalarCompanion_zero
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open Complex MeasureTheory Set
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (a b xi : ℂ) (ha : a ≠ 0) (t : ℝ) :
    crouzeixBoundaryDoubleLayerDensity (Omega.complexAffine a b ha)
        (a * xi + b) t =
      crouzeixBoundaryDoubleLayerDensity Omega xi t := by
  have hgamma : HasDerivAt Omega.boundaryParam
      (deriv Omega.boundaryParam t) t :=
    (Omega.boundaryParam_contDiff.differentiable (by norm_num) t).hasDerivAt
  have hderiv : deriv (fun s : ℝ => a * Omega.boundaryParam s + b) t =
      a * deriv Omega.boundaryParam t := by
    have hmul := (hasDerivAt_const t a).mul hgamma
    have hadd := hmul.add (hasDerivAt_const t b)
    rw [show (fun s : ℝ => a * Omega.boundaryParam s + b) =
        (fun _ : ℝ => a) * Omega.boundaryParam +
          (fun _ : ℝ => b) by
      funext s
      rfl]
    simpa only [zero_mul, zero_add, add_zero] using hadd.deriv
  unfold crouzeixBoundaryDoubleLayerDensity
  change (deriv (fun s : ℝ => a * Omega.boundaryParam s + b) t *
      (a * Omega.boundaryParam t + b - (a * xi + b))⁻¹).im /
        Real.pi = _
  rw [hderiv]
  have hsub : a * Omega.boundaryParam t + b - (a * xi + b) =
      a * (Omega.boundaryParam t - xi) := by ring
  rw [hsub, mul_inv_rev]
  congr 2
  calc
    a * deriv Omega.boundaryParam t *
          ((Omega.boundaryParam t - xi)⁻¹ * a⁻¹) =
        (a * a⁻¹) *
          (deriv Omega.boundaryParam t *
            (Omega.boundaryParam t - xi)⁻¹) := by ring
    _ = deriv Omega.boundaryParam t *
        (Omega.boundaryParam t - xi)⁻¹ := by
      rw [mul_inv_cancel₀ ha, one_mul]
