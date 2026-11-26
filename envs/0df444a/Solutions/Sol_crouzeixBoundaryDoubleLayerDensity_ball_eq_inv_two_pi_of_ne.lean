-- Prove2me | solution 1 for crouzeixBoundaryDoubleLayerDensity_ball_eq_inv_two_pi_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:45:33.156472+00:00
-- url     : https://prove2.me/submissions/0f842be0-30c3-4b14-8b6e-28ee5d2ad849

import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasure
import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasureCircle
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


section
open Complex MeasureTheory Set
open scoped ComplexConjugate Interval Real
private theorem im_circleChordLogDeriv_eq_half
    (u v : ℂ) (huv : u ≠ v)
    (hnorm : Complex.normSq u = Complex.normSq v) :
    ((u * I) * (u - v)⁻¹).im = 1 / 2 := by
  have hd : Complex.normSq (u - v) ≠ 0 := by
    intro hzero
    exact sub_ne_zero.mpr huv (Complex.normSq_eq_zero.mp hzero)
  rw [← div_eq_mul_inv, Complex.div_im, ← sub_div]
  have hnum : (u * I).im * (u - v).re -
      (u * I).re * (u - v).im = Complex.normSq (u - v) / 2 := by
    simp only [Complex.mul_im, Complex.mul_re, Complex.I_re, Complex.I_im,
      mul_zero, mul_one, add_zero, Complex.sub_re, Complex.sub_im,
      Complex.normSq_apply] at hnorm ⊢
    linarith
  rw [hnum]
  field_simp [hd]
end

set_option autoImplicit false
open Complex MeasureTheory Set
open scoped ComplexConjugate Interval Real
theorem _root_.solution
    {c xi : ℂ} {R : ℝ} (hR : 0 < R)
    (hxi : xi ∈ Metric.sphere c R) (t : ℝ)
    (hne : circleMap c R t ≠ xi) :
    crouzeixBoundaryDoubleLayerDensity
        (SmoothJordanDomain.ball c R hR) xi t = (2 * Real.pi)⁻¹ := by
  let u := circleMap 0 R t
  let v := xi - c
  have hd : circleMap c R t - xi = u - v := by
    dsimp only [u, v]
    rw [← circleMap_sub_center c R t]
    ring
  have huv : u ≠ v := by
    apply sub_ne_zero.mp
    rw [← hd]
    exact sub_ne_zero.mpr hne
  have hunorm : Complex.normSq u = R ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]
    dsimp only [u]
    rw [norm_circleMap_zero, abs_of_pos hR]
  have hvnorm : ‖v‖ = R := by
    dsimp only [v]
    simpa only [dist_eq_norm] using (Metric.mem_sphere.mp hxi)
  have hnorm : Complex.normSq u = Complex.normSq v := by
    rw [hunorm, Complex.normSq_eq_norm_sq, hvnorm]
  have hhalf := im_circleChordLogDeriv_eq_half u v huv hnorm
  unfold crouzeixBoundaryDoubleLayerDensity
  change (deriv (circleMap c R) t *
      (circleMap c R t - xi)⁻¹).im / Real.pi = _
  rw [deriv_circleMap, hd]
  change ((u * I) * (u - v)⁻¹).im / Real.pi = _
  rw [hhalf]
  field_simp [Real.pi_ne_zero]
