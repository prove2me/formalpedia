-- Prove2me | solution 1 for exists_uniform_norm_inward_regularized_integrand_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:47:27.329796+00:00
-- url     : https://prove2.me/submissions/9a738100-e921-4c48-82a5-b4700b3ec21a

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Theorems.Thm_smoothJordanInwardPoint_mem_carrier
import Theorems.Thm_exists_uniform_inward_boundary_cross_bound
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
open Complex Filter MeasureTheory Set
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) {c : ℂ}
    (hc : c ∈ Omega.carrier) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ xi ∈ frontier Omega.carrier,
        ∀ r ∈ Ioc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) (2 * Real.pi),
          ‖deriv Omega.boundaryParam t •
            (((star (Polynomial.eval (Omega.boundaryParam t) p) -
                  star (Polynomial.eval xi p)) *
                (Omega.boundaryParam t -
                  smoothJordanInwardPoint c xi r)⁻¹) -
              ((star (Polynomial.eval (Omega.boundaryParam t) p) -
                  star (Polynomial.eval xi p)) *
                (Omega.boundaryParam t - xi)⁻¹))‖ ≤
            C * (‖deriv Omega.boundaryParam t‖ *
              ‖Polynomial.eval (Omega.boundaryParam t)
                (p /ₘ (Polynomial.X - Polynomial.C xi))‖) := by
  obtain ⟨delta, R, hdelta, hR, hcross⟩ :=
    exists_uniform_inward_boundary_cross_bound Omega hc
  let C := R / delta
  refine ⟨C, div_nonneg hR hdelta.le, ?_⟩
  intro xi hxi r hr t _ht
  let q := p /ₘ (Polynomial.X - Polynomial.C xi)
  let sigma := Omega.boundaryParam t
  let z := smoothJordanInwardPoint c xi r
  have hsigma : sigma ∈ frontier Omega.carrier := by
    dsimp only [sigma]
    rw [← Omega.boundaryParam_range]
    exact mem_range_self t
  have hz : z ∈ Omega.carrier :=
    smoothJordanInwardPoint_mem_carrier Omega hc hxi hr
  have hsigmaz : sigma - z ≠ 0 := by
    apply sub_ne_zero.mpr
    intro heq
    have hsigmaCarrier : sigma ∈ Omega.carrier := heq ▸ hz
    have hempty : sigma ∈ (∅ : Set ℂ) := by
      rw [← Omega.isOpen_carrier.inter_frontier_eq]
      exact ⟨hsigmaCarrier, hsigma⟩
    exact hempty
  change
    ‖deriv Omega.boundaryParam t •
      (((star (Polynomial.eval sigma p) - star (Polynomial.eval xi p)) *
            (sigma - z)⁻¹) -
        ((star (Polynomial.eval sigma p) - star (Polynomial.eval xi p)) *
            (sigma - xi)⁻¹))‖ ≤
      C * (‖deriv Omega.boundaryParam t‖ * ‖Polynomial.eval sigma q‖)
  by_cases hsigmaXi : sigma = xi
  · rw [hsigmaXi]
    simp only [sub_self, inv_zero, mul_zero, zero_mul]
    rw [smul_zero, norm_zero]
    exact mul_nonneg (div_nonneg hR hdelta.le)
      (mul_nonneg (norm_nonneg (deriv Omega.boundaryParam t))
        (norm_nonneg (Polynomial.eval xi q)))
  have hsigmaXiSub : sigma - xi ≠ 0 := sub_ne_zero.mpr hsigmaXi
  have hpoly : Polynomial.C (Polynomial.eval xi p) +
      (Polynomial.X - Polynomial.C xi) * q = p := by
    rw [← Polynomial.modByMonic_X_sub_C_eq_C_eval p xi]
    exact Polynomial.modByMonic_add_div p
      (Polynomial.X - Polynomial.C xi)
  have heval : Polynomial.eval sigma p - Polynomial.eval xi p =
      (sigma - xi) * Polynomial.eval sigma q := by
    have h := congrArg (Polynomial.eval sigma) hpoly
    simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
      Polynomial.eval_sub, Polynomial.eval_X] at h
    rw [← h]
    ring
  have hstar :
      star (Polynomial.eval sigma p) - star (Polynomial.eval xi p) =
        star (sigma - xi) * star (Polynomial.eval sigma q) := by
    rw [← star_sub, heval, star_mul]
    ring
  have hmiddle : (sigma - xi) - (sigma - z) = z - xi := by ring
  have hnorm :
      ‖((star (Polynomial.eval sigma p) -
            star (Polynomial.eval xi p)) * (sigma - z)⁻¹) -
          ((star (Polynomial.eval sigma p) -
            star (Polynomial.eval xi p)) * (sigma - xi)⁻¹)‖ =
        ‖Polynomial.eval sigma q‖ *
          (‖z - xi‖ / ‖sigma - z‖) := by
    rw [← mul_sub, inv_sub_inv' hsigmaz hsigmaXiSub, hstar,
      norm_mul, norm_mul, norm_mul, norm_mul, norm_star, norm_star,
      norm_inv, norm_inv, hmiddle]
    field_simp [norm_ne_zero_iff.mpr hsigmaz,
      norm_ne_zero_iff.mpr hsigmaXiSub]
  have hratio : ‖z - xi‖ / ‖sigma - z‖ ≤ R / delta := by
    apply (div_le_div_iff₀ (norm_pos_iff.mpr hsigmaz) hdelta).2
    simpa only [z, sigma, mul_comm] using
      hcross xi hxi r hr sigma hsigma
  simp only [smul_eq_mul, norm_mul]
  rw [hnorm]
  calc
    ‖deriv Omega.boundaryParam t‖ *
          (‖Polynomial.eval sigma q‖ * (‖z - xi‖ / ‖sigma - z‖)) =
        (‖z - xi‖ / ‖sigma - z‖) *
          (‖deriv Omega.boundaryParam t‖ *
            ‖Polynomial.eval sigma q‖) := by ring
    _ ≤ C * (‖deriv Omega.boundaryParam t‖ *
          ‖Polynomial.eval sigma q‖) :=
      mul_le_mul_of_nonneg_right hratio
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))
