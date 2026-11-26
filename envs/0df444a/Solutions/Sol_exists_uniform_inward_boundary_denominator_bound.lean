-- Prove2me | solution 1 for exists_uniform_inward_boundary_denominator_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:45:16.407325+00:00
-- url     : https://prove2.me/submissions/0503288a-fbda-4baa-bfae-d64fcdcbfbd3

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
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
    (Omega : SmoothJordanDomain) {c : ℂ} (hc : c ∈ Omega.carrier) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ xi ∈ frontier Omega.carrier,
        ∀ r ∈ Ioc (0 : ℝ) 1, ∀ sigma ∈ frontier Omega.carrier,
          r * delta ≤ ‖sigma - smoothJordanInwardPoint c xi r‖ := by
  obtain ⟨delta, hdelta, hball⟩ :=
    Metric.isOpen_iff.mp Omega.isOpen_carrier c hc
  refine ⟨delta, hdelta, ?_⟩
  intro xi hxi r hr sigma hsigma
  apply le_of_not_gt
  intro hlt
  let z := smoothJordanInwardPoint c xi r
  let y : ℂ := c + r⁻¹ • (sigma - z)
  have hyball : y ∈ Metric.ball c delta := by
    rw [Metric.mem_ball, dist_eq_norm]
    have hnorm : ‖y - c‖ = r⁻¹ * ‖sigma - z‖ := by
      simp only [y, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hr.1)]
    rw [hnorm]
    calc
      r⁻¹ * ‖sigma - z‖ < r⁻¹ * (r * delta) :=
        mul_lt_mul_of_pos_left hlt (inv_pos.mpr hr.1)
      _ = delta := by
        rw [← mul_assoc, inv_mul_cancel₀ hr.1.ne', one_mul]
  have hy : y ∈ Omega.carrier := hball hyball
  have hyint : y ∈ interior Omega.carrier := by
    rwa [Omega.isOpen_carrier.interior_eq]
  have hcombo : (1 - r) • xi + r • y = sigma := by
    simp only [y, z, smoothJordanInwardPoint, smul_add, smul_smul,
      mul_inv_cancel₀ hr.1.ne', one_smul]
    module
  have hsigmaInt : sigma ∈ interior Omega.carrier := by
    rw [← hcombo]
    exact
      Omega.strictConvex_carrier.convex.combo_closure_interior_mem_interior
        (frontier_subset_closure hxi) hyint
        (sub_nonneg.mpr hr.2) hr.1 (by ring)
  have hsigmaCarrier : sigma ∈ Omega.carrier := interior_subset hsigmaInt
  have hempty : sigma ∈ (∅ : Set ℂ) := by
    rw [← Omega.isOpen_carrier.inter_frontier_eq]
    exact ⟨hsigmaCarrier, hsigma⟩
  exact hempty
