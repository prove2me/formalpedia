-- Prove2me | solution 1 for crouzeixPolynomialScalarCompanionRegularized_ball_boundary_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:45:13.986357+00:00
-- url     : https://prove2.me/submissions/6322d966-3295-4e43-a5f8-ab5207cf1457

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
import Theorems.Thm_crouzeixPolynomialScalarCompanion_ball_eq_eval_zero
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
section AuxiliaryOperator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
end AuxiliaryOperator
end

set_option autoImplicit false
open Complex ComplexConjugate Filter Polynomial Set
open scoped Interval Real
theorem _root_.solution
    {R : ℝ} (hR : 0 < R) (p : Polynomial ℂ) {xi : ℂ}
    (hxi : xi ∈ Metric.sphere (0 : ℂ) R) :
    crouzeixPolynomialScalarCompanionRegularized
        (SmoothJordanDomain.ball 0 R hR) p xi xi =
      star (Polynomial.eval 0 p) - star (Polynomial.eval xi p) := by
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
  have hxi' : xi ∈ Metric.sphere (0 : ℂ) |R| := by
    simpa only [abs_of_pos hR] using hxi
  let c : ℂ := -((R : ℂ) ^ 2) * xi⁻¹
  have hintegral :
      circleIntegral
          (fun sigma ↦
            (star (Polynomial.eval sigma p) - star (Polynomial.eval xi p)) *
              (sigma - xi)⁻¹)
          0 R =
        circleIntegral
          (fun sigma ↦ c *
            (star (Polynomial.eval sigma q) * sigma⁻¹))
          0 R := by
    apply circleIntegral.circleIntegral_congr_codiscreteWithin
    · filter_upwards [compl_singleton_mem_codiscreteWithin
          (s := Metric.sphere (0 : ℂ) |R|) xi,
        Filter.self_mem_codiscreteWithin (Metric.sphere (0 : ℂ) |R|)]
        with sigma hsigma_ne hsigma
      have hsigma_ne' : sigma ≠ xi := by simpa only [mem_compl_iff, mem_singleton_iff] using hsigma_ne
      have hsigma0 := ne_zero_of_mem_centered_sphere hR hsigma
      have hxi0 := ne_zero_of_mem_centered_sphere hR hxi'
      have hstar_sigma := star_eq_sq_mul_inv_of_mem_centered_sphere hR hsigma
      have hstar_xi := star_eq_sq_mul_inv_of_mem_centered_sphere hR hxi'
      have hstar_eval :
          star (Polynomial.eval sigma p) - star (Polynomial.eval xi p) =
            star (sigma - xi) * star (Polynomial.eval sigma q) := by
        rw [← star_sub, heval sigma, star_mul]
        ring
      rw [hstar_eval, star_sub, hstar_sigma, hstar_xi]
      dsimp only [c]
      field_simp [hsigma0, hxi0, hsigma_ne']
      all_goals ring
    · exact hR.ne'
  have hqcomp := crouzeixPolynomialScalarCompanion_ball_eq_eval_zero
    hR q (Metric.mem_ball_self hR)
  have hqintegral :
      (2 * (Real.pi : ℂ) * I)⁻¹ *
          circleIntegral
            (fun sigma ↦ star (Polynomial.eval sigma q) * sigma⁻¹) 0 R =
        star (Polynomial.eval 0 q) := by
    unfold crouzeixPolynomialScalarCompanion at hqcomp
    change (2 * (Real.pi : ℂ) * I)⁻¹ *
        contourIntegral
          (fun sigma ↦ star (Polynomial.eval sigma q) * (sigma - 0)⁻¹)
          (circleMap 0 R) = star (Polynomial.eval 0 q) at hqcomp
    rw [contourIntegral_circleMap] at hqcomp
    simpa only [sub_zero] using hqcomp
  have hcq : c * star (Polynomial.eval 0 q) =
      star (Polynomial.eval 0 p) - star (Polynomial.eval xi p) := by
    have h0 := heval 0
    calc
      c * star (Polynomial.eval 0 q) =
          star (-xi * Polynomial.eval 0 q) := by
        rw [star_mul, star_neg,
          star_eq_sq_mul_inv_of_mem_centered_sphere hR hxi']
        dsimp only [c]
        ring
      _ = star (Polynomial.eval 0 p - Polynomial.eval xi p) := by
        rw [h0, zero_sub]
      _ = star (Polynomial.eval 0 p) - star (Polynomial.eval xi p) := star_sub _ _
  change (2 * (Real.pi : ℂ) * I)⁻¹ *
      circleIntegral
        (fun sigma ↦
          (star (Polynomial.eval sigma p) - star (Polynomial.eval xi p)) *
            (sigma - xi)⁻¹)
        0 R = _
  rw [hintegral, circleIntegral.integral_const_mul]
  calc
    (2 * (Real.pi : ℂ) * I)⁻¹ *
          (c * circleIntegral
            (fun sigma ↦ star (Polynomial.eval sigma q) * sigma⁻¹) 0 R) =
        c * ((2 * (Real.pi : ℂ) * I)⁻¹ *
          circleIntegral
            (fun sigma ↦ star (Polynomial.eval sigma q) * sigma⁻¹) 0 R) := by ring
    _ = c * star (Polynomial.eval 0 q) := by rw [hqintegral]
    _ = star (Polynomial.eval 0 p) - star (Polynomial.eval xi p) := hcq
