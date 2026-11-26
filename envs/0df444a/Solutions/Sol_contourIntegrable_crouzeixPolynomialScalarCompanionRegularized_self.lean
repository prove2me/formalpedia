-- Prove2me | solution 1 for contourIntegrable_crouzeixPolynomialScalarCompanionRegularized_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:09:12.092377+00:00
-- url     : https://prove2.me/submissions/ad0a19c6-96c0-424d-a45e-ad3e6bcbe171

import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundary
import Mathlib.Algebra.Polynomial.FieldDivision
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionBoundaryValue_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionDeriv_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanion_zero
import Theorems.Thm_mem_numericalRange
attribute [local simp] crouzeixPolynomialScalarCompanionDeriv_zero
attribute [local simp] crouzeixPolynomialScalarCompanion_zero
attribute [local simp] mem_numericalRange


attribute [local simp] crouzeixPolynomialScalarCompanionRegularized_zero
attribute [local simp] crouzeixPolynomialScalarCompanionBoundaryValue_zero

set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (xi : ℂ) :
    ContourIntegrable
      (fun sigma ↦
        (star (Polynomial.eval sigma p) - star (Polynomial.eval xi p)) *
          (sigma - xi)⁻¹)
      Omega.boundaryParam := by
  let q := p /ₘ (Polynomial.X - Polynomial.C xi)
  have hpoly : Polynomial.C (Polynomial.eval xi p) +
      (Polynomial.X - Polynomial.C xi) * q = p := by
    rw [← Polynomial.modByMonic_X_sub_C_eq_C_eval p xi]
    exact Polynomial.modByMonic_add_div p (Polynomial.X - Polynomial.C xi)
  have heval : ∀ sigma : ℂ,
      Polynomial.eval sigma p - Polynomial.eval xi p =
        (sigma - xi) * Polynomial.eval sigma q := by
    intro sigma
    have h := congrArg (Polynomial.eval sigma) hpoly
    simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
      Polynomial.eval_sub, Polynomial.eval_X] at h
    rw [← h]
    ring
  let F : ℝ → ℂ := fun t ↦
    deriv Omega.boundaryParam t *
      ((star (Polynomial.eval (Omega.boundaryParam t) p) -
          star (Polynomial.eval xi p)) *
        (Omega.boundaryParam t - xi)⁻¹)
  let bound : ℝ → ℝ := fun t ↦
    ‖deriv Omega.boundaryParam t‖ *
      ‖Polynomial.eval (Omega.boundaryParam t) q‖
  have hboundCont : Continuous bound := by
    exact (Omega.boundaryParam_contDiff.continuous_deriv (by norm_num)).norm.mul
      (q.continuous.comp
        Omega.boundaryParam_contDiff.continuous).norm
  have hboundInt : IntervalIntegrable bound volume
      (0 : ℝ) (2 * Real.pi) := hboundCont.intervalIntegrable _ _
  have hFstrong : StronglyMeasurable F := by
    dsimp only [F]
    exact
      (Omega.boundaryParam_contDiff.continuous_deriv
          (by norm_num)).stronglyMeasurable.mul
        (((p.continuous.comp Omega.boundaryParam_contDiff.continuous).star.sub
            continuous_const).stronglyMeasurable.mul
          ((Omega.boundaryParam_contDiff.continuous.stronglyMeasurable.sub
            stronglyMeasurable_const).inv₀))
  have hnorm : ∀ t, ‖F t‖ ≤ bound t := by
    intro t
    by_cases hzero : Omega.boundaryParam t = xi
    · simp only [F, bound, hzero, sub_self, inv_zero, mul_zero, norm_zero]
      positivity
    · have hdiff : Omega.boundaryParam t - xi ≠ 0 :=
        sub_ne_zero.mpr hzero
      have hdiffNorm : ‖Omega.boundaryParam t - xi‖ ≠ 0 :=
        norm_ne_zero_iff.mpr hdiff
      have hstar :
          star (Polynomial.eval (Omega.boundaryParam t) p) -
              star (Polynomial.eval xi p) =
            star (Omega.boundaryParam t - xi) *
              star (Polynomial.eval (Omega.boundaryParam t) q) := by
        rw [← star_sub, heval, star_mul]
        ring
      dsimp only [F, bound]
      rw [hstar]
      simp only [norm_mul, norm_star, norm_inv]
      calc
        ‖deriv Omega.boundaryParam t‖ *
              ((‖Omega.boundaryParam t - xi‖ *
                  ‖Polynomial.eval (Omega.boundaryParam t) q‖) *
                ‖Omega.boundaryParam t - xi‖⁻¹) =
            ‖deriv Omega.boundaryParam t‖ *
              (‖Polynomial.eval (Omega.boundaryParam t) q‖ *
                (‖Omega.boundaryParam t - xi‖ *
                  ‖Omega.boundaryParam t - xi‖⁻¹)) := by ring
        _ = ‖deriv Omega.boundaryParam t‖ *
              ‖Polynomial.eval (Omega.boundaryParam t) q‖ := by
          rw [mul_inv_cancel₀ hdiffNorm, mul_one]
        _ ≤ ‖deriv Omega.boundaryParam t‖ *
              ‖Polynomial.eval (Omega.boundaryParam t) q‖ := le_rfl
  unfold ContourIntegrable
  change IntervalIntegrable F volume (0 : ℝ) (2 * Real.pi)
  exact hboundInt.mono_fun hFstrong.aestronglyMeasurable.restrict
    (Eventually.of_forall fun t ↦ by
      change ‖F t‖ ≤ ‖bound t‖
      rw [Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
      exact hnorm t)
