-- Prove2me | solution 1 for crouzeixPolynomialScalarCompanionBoundaryValue_eq_integral_boundaryDoubleLayerDensity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:01:26.053746+00:00
-- url     : https://prove2.me/submissions/21e88a82-149a-46c5-a74f-6c0fca60990c

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPhaseInduction
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasure
import Theorems.Thm_ofReal_crouzeixBoundaryDoubleLayerDensity
import Theorems.Thm_contourIntegral_polynomial_eval_eq_zero
import Theorems.Thm_ContourIntegrable_of_continuousOn
import Theorems.Thm_ae_boundaryParam_ne_of_mem_frontier
import Theorems.Thm_contourIntegrable_crouzeixPolynomialScalarCompanionRegularized_self
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
open Complex MeasureTheory Polynomial Set
open scoped ComplexConjugate Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) {xi : ℂ}
    (hxi : xi ∈ frontier Omega.carrier)
    (hrho : IntervalIntegrable
      (crouzeixBoundaryDoubleLayerDensity Omega xi)
      volume 0 (2 * Real.pi))
    (hmass : (∫ t in (0 : ℝ)..(2 * Real.pi),
      crouzeixBoundaryDoubleLayerDensity Omega xi t) = 1) :
    crouzeixPolynomialScalarCompanionBoundaryValue Omega p xi =
      ∫ t in (0 : ℝ)..(2 * Real.pi),
        (crouzeixBoundaryDoubleLayerDensity Omega xi t : ℂ) *
          star (Polynomial.eval (Omega.boundaryParam t) p) := by
  let q := p /ₘ (Polynomial.X - Polynomial.C xi)
  let gamma := Omega.boundaryParam
  let rho := crouzeixBoundaryDoubleLayerDensity Omega xi
  let c : ℂ := (2 * (Real.pi : ℂ) * I)⁻¹
  have heval : ∀ z : ℂ,
      Polynomial.eval z p - Polynomial.eval xi p =
        (z - xi) * Polynomial.eval z q := by
    intro z
    have hpoly : Polynomial.C (Polynomial.eval xi p) +
        (Polynomial.X - Polynomial.C xi) * q = p := by
      dsimp only [q]
      rw [← Polynomial.modByMonic_X_sub_C_eq_C_eval p xi]
      exact Polynomial.modByMonic_add_div p
        (Polynomial.X - Polynomial.C xi)
    have h := congrArg (Polynomial.eval z) hpoly
    simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
      Polynomial.eval_sub, Polynomial.eval_X] at h
    rw [← h]
    ring
  have hrhoC : IntervalIntegrable (fun t => (rho t : ℂ))
      volume 0 (2 * Real.pi) := by
    constructor
    · change IntegrableOn (fun t => Complex.ofRealCLM (rho t))
        (Ioc 0 (2 * Real.pi)) volume
      exact Complex.ofRealCLM.integrable_comp hrho.1
    · change IntegrableOn (fun t => Complex.ofRealCLM (rho t))
        (Ioc (2 * Real.pi) 0) volume
      exact Complex.ofRealCLM.integrable_comp hrho.2
  have hpcont : Continuous (fun t : ℝ =>
      star (Polynomial.eval (gamma t) p)) := by
    exact p.continuous.comp
      Omega.boundaryParam_contDiff.continuous |>.star
  have hweighted : IntervalIntegrable
      (fun t => (rho t : ℂ) * star (Polynomial.eval (gamma t) p))
      volume 0 (2 * Real.pi) :=
    hrhoC.mul_continuousOn hpcont.continuousOn
  have hdiffWeighted : IntervalIntegrable
      (fun t => (rho t : ℂ) *
        (star (Polynomial.eval (gamma t) p) -
          star (Polynomial.eval xi p)))
      volume 0 (2 * Real.pi) := by
    apply hrhoC.mul_continuousOn
    exact (hpcont.sub continuous_const).continuousOn
  let u : ℝ → ℂ := fun t => deriv gamma t *
    ((star (Polynomial.eval (gamma t) p) - star (Polynomial.eval xi p)) *
      (gamma t - xi)⁻¹)
  let v : ℝ → ℂ := fun t =>
    deriv gamma t * Polynomial.eval (gamma t) q
  have hu : IntervalIntegrable u volume 0 (2 * Real.pi) := by
    have h :=
      contourIntegrable_crouzeixPolynomialScalarCompanionRegularized_self
        Omega p xi
    change IntervalIntegrable
      (fun t => deriv gamma t *
        ((star (Polynomial.eval (gamma t) p) -
            star (Polynomial.eval xi p)) * (gamma t - xi)⁻¹))
      volume 0 (2 * Real.pi) at h
    exact h
  have hv : IntervalIntegrable v volume 0 (2 * Real.pi) := by
    have hcontour : ContourIntegrable
        (fun z => Polynomial.eval z q) gamma := by
      apply ContourIntegrable.of_continuousOn
      · exact Omega.boundaryParam_contDiff.continuous.continuousOn
      · exact
          (Omega.boundaryParam_contDiff.continuous_deriv
            (by norm_num)).continuousOn
      · exact q.continuous.continuousOn
    change IntervalIntegrable
      (fun t => deriv gamma t * Polynomial.eval (gamma t) q)
      volume 0 (2 * Real.pi) at hcontour
    exact hcontour
  have hvstar : IntervalIntegrable (fun t => star (v t))
      volume 0 (2 * Real.pi) := by
    constructor
    · change IntegrableOn (fun t =>
        Complex.conjLIE.toLinearIsometry.toContinuousLinearMap (v t))
        (Ioc 0 (2 * Real.pi)) volume
      exact
        Complex.conjLIE.toLinearIsometry.toContinuousLinearMap.integrable_comp
          hv.1
    · change IntegrableOn (fun t =>
        Complex.conjLIE.toLinearIsometry.toContinuousLinearMap (v t))
        (Ioc (2 * Real.pi) 0) volume
      exact
        Complex.conjLIE.toLinearIsometry.toContinuousLinearMap.integrable_comp
          hv.2
  have hvzero : (∫ t in (0 : ℝ)..(2 * Real.pi), v t) = 0 := by
    simpa only [v, gamma, contourIntegral, smul_eq_mul] using
      contourIntegral_polynomial_eval_eq_zero Omega q
  have hpoint : ∀ t, gamma t ≠ xi →
      (rho t : ℂ) *
          (star (Polynomial.eval (gamma t) p) -
            star (Polynomial.eval xi p)) =
        c * (u t - star (v t)) := by
    intro t hne
    rw [show (rho t : ℂ) =
        (2 * (Real.pi : ℂ) * I)⁻¹ *
          (deriv Omega.boundaryParam t *
              (Omega.boundaryParam t - xi)⁻¹ -
            star (deriv Omega.boundaryParam t *
              (Omega.boundaryParam t - xi)⁻¹)) by
          exact ofReal_crouzeixBoundaryDoubleLayerDensity Omega xi t]
    dsimp only [c, u, v, gamma]
    rw [← star_sub, heval]
    simp only [star_mul]
    have hd : Omega.boundaryParam t - xi ≠ 0 := sub_ne_zero.mpr hne
    have hstarCancel :
        star ((Omega.boundaryParam t - xi)⁻¹) *
          star (Omega.boundaryParam t - xi) = 1 :=
      by
        rw [star_inv₀, inv_mul_cancel₀ (star_ne_zero.mpr hd)]
    calc
      (2 * (Real.pi : ℂ) * I)⁻¹ *
            (deriv Omega.boundaryParam t *
                (Omega.boundaryParam t - xi)⁻¹ -
              star ((Omega.boundaryParam t - xi)⁻¹) *
                star (deriv Omega.boundaryParam t)) *
          (star (Polynomial.eval (Omega.boundaryParam t) q) *
            star (Omega.boundaryParam t - xi)) =
          (2 * (Real.pi : ℂ) * I)⁻¹ *
            (deriv Omega.boundaryParam t *
                ((star (Polynomial.eval (Omega.boundaryParam t) q) *
                    star (Omega.boundaryParam t - xi)) *
                  (Omega.boundaryParam t - xi)⁻¹) -
              star (Polynomial.eval (Omega.boundaryParam t) q) *
                star (deriv Omega.boundaryParam t) *
                  (star ((Omega.boundaryParam t - xi)⁻¹) *
                    star (Omega.boundaryParam t - xi))) := by
        ring
      _ = (2 * (Real.pi : ℂ) * I)⁻¹ *
          (deriv Omega.boundaryParam t *
              ((star (Polynomial.eval (Omega.boundaryParam t) q) *
                  star (Omega.boundaryParam t - xi)) *
                (Omega.boundaryParam t - xi)⁻¹) -
            star (Polynomial.eval (Omega.boundaryParam t) q) *
              star (deriv Omega.boundaryParam t)) := by
        rw [hstarCancel, mul_one]
  have hdiffIntegral :
      (∫ t in (0 : ℝ)..(2 * Real.pi),
        (rho t : ℂ) *
          (star (Polynomial.eval (gamma t) p) -
            star (Polynomial.eval xi p))) =
        c * (∫ t in (0 : ℝ)..(2 * Real.pi), u t) := by
    calc
      (∫ t in (0 : ℝ)..(2 * Real.pi),
          (rho t : ℂ) *
            (star (Polynomial.eval (gamma t) p) -
              star (Polynomial.eval xi p))) =
          ∫ t in (0 : ℝ)..(2 * Real.pi), c * (u t - star (v t)) := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [ae_boundaryParam_ne_of_mem_frontier Omega hxi]
          with t ht
        intro _ht
        exact hpoint t (ht _ht)
      _ = c * ((∫ t in (0 : ℝ)..(2 * Real.pi), u t) -
          ∫ t in (0 : ℝ)..(2 * Real.pi), star (v t)) := by
        rw [intervalIntegral.integral_const_mul,
          intervalIntegral.integral_sub hu hvstar]
      _ = c * ((∫ t in (0 : ℝ)..(2 * Real.pi), u t) -
          star (∫ t in (0 : ℝ)..(2 * Real.pi), v t)) := by
        rw [show (∫ t in (0 : ℝ)..(2 * Real.pi), star (v t)) =
            star (∫ t in (0 : ℝ)..(2 * Real.pi), v t) by
          change (∫ t in (0 : ℝ)..(2 * Real.pi),
            (starRingEnd ℂ) (v t)) =
              (starRingEnd ℂ) (∫ t in (0 : ℝ)..(2 * Real.pi), v t)
          exact intervalIntegral.intervalIntegral_conj]
      _ = c * (∫ t in (0 : ℝ)..(2 * Real.pi), u t) := by
        rw [hvzero, star_zero, sub_zero]
  have hsplit :
      (∫ t in (0 : ℝ)..(2 * Real.pi),
        (rho t : ℂ) * star (Polynomial.eval (gamma t) p)) =
        star (Polynomial.eval xi p) +
          c * (∫ t in (0 : ℝ)..(2 * Real.pi), u t) := by
    have hconst : IntervalIntegrable
        (fun t => star (Polynomial.eval xi p) * (rho t : ℂ))
        volume 0 (2 * Real.pi) := hrhoC.const_mul _
    have hfun :
        (fun t => (rho t : ℂ) * star (Polynomial.eval (gamma t) p)) =
          fun t => star (Polynomial.eval xi p) * (rho t : ℂ) +
            (rho t : ℂ) *
              (star (Polynomial.eval (gamma t) p) -
                star (Polynomial.eval xi p)) := by
      funext t
      ring
    rw [hfun, intervalIntegral.integral_add hconst hdiffWeighted,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_ofReal, hmass, ofReal_one, mul_one,
      hdiffIntegral]
  unfold crouzeixPolynomialScalarCompanionBoundaryValue
  unfold crouzeixPolynomialScalarCompanionRegularized
  change star (Polynomial.eval xi p) +
      c * (∫ t in (0 : ℝ)..(2 * Real.pi), u t) = _
  simpa only [rho, gamma] using hsplit.symm
