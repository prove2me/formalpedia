-- Prove2me | solution 1 for hasDerivAt_contourIntegral_resolvent_affineOperator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:29:18.257671+00:00
-- url     : https://prove2.me/submissions/58ec3981-74e9-4e9e-9e85-a48d46c06199

import Definitions.Def_Operator_Crouzeix_ScalarCauchyKernelWinding
import Definitions.Def_Operator_SpectralSet_SpectrumInNR
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Definitions.Def_Operator_Crouzeix_ResolventContourHomotopy
import Theorems.Thm_hasDerivAt_resolvent_affineOperator
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
    {epsilon C : ℝ} (hepsilon : 0 < epsilon) (hC : 0 ≤ C)
    (hres : ∀ w ∈ ball s epsilon, ∀ t : ℝ,
      Omega.boundaryParam t ∈ resolventSet ℂ (B + w • D))
    (hbound : ∀ w ∈ ball s epsilon, ∀ t : ℝ,
      ‖resolvent (B + w • D) (Omega.boundaryParam t)‖ ≤ C) :
    HasDerivAt
      (fun w : ℂ =>
        contourIntegral (resolvent (B + w • D)) Omega.boundaryParam)
      (contourIntegral
        (fun z : ℂ =>
          resolvent (B + s • D) z * D * resolvent (B + s • D) z)
        Omega.boundaryParam) s := by
  let F : ℂ → ℝ → (E →L[ℂ] E) := fun w t =>
    deriv Omega.boundaryParam t •
      resolvent (B + w • D) (Omega.boundaryParam t)
  let F' : ℂ → ℝ → (E →L[ℂ] E) := fun w t =>
    deriv Omega.boundaryParam t •
      (resolvent (B + w • D) (Omega.boundaryParam t) * D *
        resolvent (B + w • D) (Omega.boundaryParam t))
  let bound : ℝ → ℝ := fun t =>
    ‖deriv Omega.boundaryParam t‖ * (C * ‖D‖ * C)
  have hFcont : ∀ w ∈ ball s epsilon, Continuous (F w) := by
    intro w hw
    have hRcont : Continuous
        (fun t => resolvent (B + w • D) (Omega.boundaryParam t)) := by
      rw [continuous_iff_continuousAt]
      intro t
      exact (spectrum.hasDerivAt_resolvent_const_left
        (hres w hw t)).continuousAt.comp_of_eq
          (Omega.boundaryParam_contDiff.continuous.continuousAt) rfl
    exact (Omega.boundaryParam_contDiff.continuous_deriv
      (by norm_num)).smul hRcont
  have hF'cont : ∀ w ∈ ball s epsilon, Continuous (F' w) := by
    intro w hw
    have hRcont : Continuous
        (fun t => resolvent (B + w • D) (Omega.boundaryParam t)) := by
      rw [continuous_iff_continuousAt]
      intro t
      exact (spectrum.hasDerivAt_resolvent_const_left
        (hres w hw t)).continuousAt.comp_of_eq
          (Omega.boundaryParam_contDiff.continuous.continuousAt) rfl
    exact (Omega.boundaryParam_contDiff.continuous_deriv
      (by norm_num)).smul ((hRcont.mul continuous_const).mul hRcont)
  have hboundInt : IntervalIntegrable bound volume 0 (2 * Real.pi) := by
    apply Continuous.intervalIntegrable
    exact (Omega.boundaryParam_contDiff.continuous_deriv
      (by norm_num)).norm.mul continuous_const
  have hFmeas : ∀ᶠ w in nhds s,
      AEStronglyMeasurable (F w) (volume.restrict (Ι (0 : ℝ) (2 * Real.pi))) := by
    filter_upwards [ball_mem_nhds s hepsilon] with w hw
    exact (hFcont w hw).aestronglyMeasurable.restrict
  have hFint : IntervalIntegrable (F s) volume 0 (2 * Real.pi) :=
    (hFcont s (mem_ball_self hepsilon)).intervalIntegrable 0 (2 * Real.pi)
  have hF'meas : AEStronglyMeasurable (F' s)
      (volume.restrict (Ι (0 : ℝ) (2 * Real.pi))) :=
    (hF'cont s (mem_ball_self hepsilon)).aestronglyMeasurable.restrict
  have hderiv : ∀ᵐ t ∂volume, t ∈ Ι (0 : ℝ) (2 * Real.pi) →
      ∀ w ∈ ball s epsilon, HasDerivAt (fun x => F x t) (F' w t) w := by
    filter_upwards [] with t _ w hw
    exact (hasDerivAt_resolvent_affineOperator B D w
      (Omega.boundaryParam t) (hres w hw t)).const_smul
        (deriv Omega.boundaryParam t)
  have hnorm : ∀ᵐ t ∂volume, t ∈ Ι (0 : ℝ) (2 * Real.pi) →
      ∀ w ∈ ball s epsilon, ‖F' w t‖ ≤ bound t := by
    filter_upwards [] with t _ w hw
    rw [norm_smul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    calc
      ‖resolvent (B + w • D) (Omega.boundaryParam t) * D *
          resolvent (B + w • D) (Omega.boundaryParam t)‖ ≤
          ‖resolvent (B + w • D) (Omega.boundaryParam t)‖ * ‖D‖ *
            ‖resolvent (B + w • D) (Omega.boundaryParam t)‖ := by
        exact (norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ C * ‖D‖ * C := by
        gcongr
        · exact hbound w hw t
        · exact hbound w hw t
  obtain ⟨_, hdiff⟩ :=
    intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (s := ball s epsilon) (bound := bound) (ball_mem_nhds s hepsilon)
      hFmeas hFint hF'meas hnorm hboundInt hderiv
  simpa only [contourIntegral, F, F'] using hdiff
