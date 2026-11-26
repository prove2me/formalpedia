-- Prove2me | solution 1 for crouzeixPolynomialScalarCompanionRegularized_ball_center_boundary_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:40:35.457072+00:00
-- url     : https://prove2.me/submissions/819118e2-ed4c-4221-b339-fa83aa6c8cec

import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Definitions.Def_Operator_Crouzeix_ProductBase
import Definitions.Def_Operator_Crouzeix_ScalarCompanionCircle
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljCircle
import Theorems.Thm_Polynomial_aeval_affineComposition
import Theorems.Thm_Polynomial_eval_affineComposition
import Theorems.Thm_contourIntegral_circleMap
import Theorems.Thm_crouzeixPolynomialScalarCompanionBoundaryValue_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionDeriv_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanion_ball_center_eq_eval_center
import Theorems.Thm_crouzeixPolynomialScalarCompanion_zero
import Theorems.Thm_mem_numericalRange
attribute [local simp] Polynomial.aeval_affineComposition
attribute [local simp] Polynomial.eval_affineComposition
attribute [local simp] crouzeixPolynomialScalarCompanionBoundaryValue_zero
attribute [local simp] crouzeixPolynomialScalarCompanionDeriv_zero
attribute [local simp] crouzeixPolynomialScalarCompanionRegularized_zero
attribute [local simp] crouzeixPolynomialScalarCompanion_zero
attribute [local simp] mem_numericalRange


section
open Complex ComplexConjugate Filter Polynomial Set
open scoped Interval Real
private theorem star_eq_sq_mul_inv_of_mem_centered_sphere
    {R : ℝ} (hR : 0 < R) {z : ℂ}
    (hz : z ∈ Metric.sphere (0 : ℂ) |R|) :
    star z = (R : ℂ) ^ 2 * z⁻¹ := by
  rw [← range_circleMap] at hz
  obtain ⟨t, rfl⟩ := hz
  change conj (circleMap 0 R t) = _
  rw [conj_circleMap_zero, circleMap_zero_inv]
  simp only [circleMap_zero, ofReal_neg, neg_mul, ofReal_inv]
  field_simp [Complex.ofReal_ne_zero.mpr hR.ne']
private theorem ne_zero_of_mem_centered_sphere
    {R : ℝ} (hR : 0 < R) {z : ℂ}
    (hz : z ∈ Metric.sphere (0 : ℂ) |R|) : z ≠ 0 := by
  intro hzero
  rw [hzero, Metric.mem_sphere, dist_self, abs_of_pos hR] at hz
  linarith
private theorem star_sub_center_eq_sq_mul_inv_of_mem_sphere
    (c : ℂ) {R : ℝ} (hR : 0 < R) {z : ℂ}
    (hz : z ∈ Metric.sphere c |R|) :
    star (z - c) = (R : ℂ) ^ 2 * (z - c)⁻¹ := by
  apply star_eq_sq_mul_inv_of_mem_centered_sphere hR
  rw [Metric.mem_sphere, dist_zero_right]
  simpa only [Metric.mem_sphere, dist_eq_norm] using hz
private theorem sub_center_ne_zero_of_mem_sphere
    (c : ℂ) {R : ℝ} (hR : 0 < R) {z : ℂ}
    (hz : z ∈ Metric.sphere c |R|) : z - c ≠ 0 := by
  apply ne_zero_of_mem_centered_sphere hR
  rw [Metric.mem_sphere, dist_zero_right]
  simpa only [Metric.mem_sphere, dist_eq_norm] using hz
section AuxiliaryOperator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
end AuxiliaryOperator
end

set_option autoImplicit false
open Complex ComplexConjugate Filter Polynomial Set
open scoped Interval Real
theorem _root_.solution
    (c : ℂ) {R : ℝ} (hR : 0 < R) (p : Polynomial ℂ) {xi : ℂ}
    (hxi : xi ∈ Metric.sphere c R) :
    crouzeixPolynomialScalarCompanionRegularized
        (SmoothJordanDomain.ball c R hR) p xi xi =
      star (Polynomial.eval c p) - star (Polynomial.eval xi p) := by
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
  have hxi' : xi ∈ Metric.sphere c |R| := by
    simpa only [abs_of_pos hR] using hxi
  let factor : ℂ := -((R : ℂ) ^ 2) * (xi - c)⁻¹
  have hintegral :
      circleIntegral
          (fun sigma ↦
            (star (Polynomial.eval sigma p) - star (Polynomial.eval xi p)) *
              (sigma - xi)⁻¹)
          c R =
        circleIntegral
          (fun sigma ↦ factor *
            (star (Polynomial.eval sigma q) * (sigma - c)⁻¹))
          c R := by
    apply circleIntegral.circleIntegral_congr_codiscreteWithin
    · filter_upwards [compl_singleton_mem_codiscreteWithin
          (s := Metric.sphere c |R|) xi,
        Filter.self_mem_codiscreteWithin (Metric.sphere c |R|)]
        with sigma hsigma_ne hsigma
      have hsigma_ne' : sigma ≠ xi := by
        simpa only [mem_compl_iff, mem_singleton_iff] using hsigma_ne
      have hdiff : -xi + sigma ≠ 0 := by
        simpa only [sub_eq_add_neg, add_comm] using sub_ne_zero.mpr hsigma_ne'
      have hcenterDiff : sigma - c - (xi - c) ≠ 0 := by
        simpa only [sub_sub_sub_cancel_right] using sub_ne_zero.mpr hsigma_ne'
      have hsigma0 := sub_center_ne_zero_of_mem_sphere c hR hsigma
      have hxi0 := sub_center_ne_zero_of_mem_sphere c hR hxi'
      have hstar_sigma :=
        star_sub_center_eq_sq_mul_inv_of_mem_sphere c hR hsigma
      have hstar_xi :=
        star_sub_center_eq_sq_mul_inv_of_mem_sphere c hR hxi'
      have hstar_eval :
          star (Polynomial.eval sigma p) - star (Polynomial.eval xi p) =
            star (sigma - xi) * star (Polynomial.eval sigma q) := by
        rw [← star_sub, heval sigma, star_mul]
        ring
      rw [hstar_eval, show sigma - xi = (sigma - c) - (xi - c) by ring,
        star_sub, hstar_sigma, hstar_xi]
      dsimp only [factor]
      field_simp [hsigma0, hxi0, hsigma_ne', hdiff]
      all_goals
        try field_simp [hcenterDiff]
        ring
    · exact hR.ne'
  have hqcomp := crouzeixPolynomialScalarCompanion_ball_center_eq_eval_center
    c hR q (Metric.mem_ball_self hR)
  have hqintegral :
      (2 * (Real.pi : ℂ) * I)⁻¹ *
          circleIntegral
            (fun sigma ↦
              star (Polynomial.eval sigma q) * (sigma - c)⁻¹) c R =
        star (Polynomial.eval c q) := by
    unfold crouzeixPolynomialScalarCompanion at hqcomp
    change (2 * (Real.pi : ℂ) * I)⁻¹ *
        contourIntegral
          (fun sigma ↦ star (Polynomial.eval sigma q) * (sigma - c)⁻¹)
          (circleMap c R) = star (Polynomial.eval c q) at hqcomp
    rw [contourIntegral_circleMap] at hqcomp
    exact hqcomp
  have hfactor : factor * star (Polynomial.eval c q) =
      star (Polynomial.eval c p) - star (Polynomial.eval xi p) := by
    have hc := heval c
    have hstar_cxi : star (c - xi) = factor := by
      rw [show c - xi = -(xi - c) by ring, star_neg,
        star_sub_center_eq_sq_mul_inv_of_mem_sphere c hR hxi']
      dsimp only [factor]
      ring
    calc
      factor * star (Polynomial.eval c q) =
          star ((c - xi) * Polynomial.eval c q) := by
        rw [star_mul, hstar_cxi]
        ring
      _ = star (Polynomial.eval c p - Polynomial.eval xi p) := by rw [hc]
      _ = star (Polynomial.eval c p) - star (Polynomial.eval xi p) := star_sub _ _
  change (2 * (Real.pi : ℂ) * I)⁻¹ *
      circleIntegral
        (fun sigma ↦
          (star (Polynomial.eval sigma p) - star (Polynomial.eval xi p)) *
            (sigma - xi)⁻¹)
        c R = _
  rw [hintegral, circleIntegral.integral_const_mul]
  calc
    (2 * (Real.pi : ℂ) * I)⁻¹ *
          (factor * circleIntegral
            (fun sigma ↦
              star (Polynomial.eval sigma q) * (sigma - c)⁻¹) c R) =
        factor * ((2 * (Real.pi : ℂ) * I)⁻¹ *
          circleIntegral
            (fun sigma ↦
              star (Polynomial.eval sigma q) * (sigma - c)⁻¹) c R) := by ring
    _ = factor * star (Polynomial.eval c q) := by rw [hqintegral]
    _ = star (Polynomial.eval c p) - star (Polynomial.eval xi p) := hfactor
