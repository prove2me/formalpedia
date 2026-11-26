-- Prove2me | solution 1 for exists_uniform_inward_boundary_cross_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:46:14.891472+00:00
-- url     : https://prove2.me/submissions/7c246138-9add-427e-a354-ebc99f5686b6

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Theorems.Thm_exists_uniform_inward_boundary_denominator_bound
import Theorems.Thm_SmoothJordanDomain_isCompact_frontier
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
    ∃ delta R : ℝ, 0 < delta ∧ 0 ≤ R ∧
      ∀ xi ∈ frontier Omega.carrier,
        ∀ r ∈ Ioc (0 : ℝ) 1, ∀ sigma ∈ frontier Omega.carrier,
          delta * ‖smoothJordanInwardPoint c xi r - xi‖ ≤
            R * ‖sigma - smoothJordanInwardPoint c xi r‖ := by
  obtain ⟨delta, hdelta, hbound⟩ :=
    exists_uniform_inward_boundary_denominator_bound Omega hc
  let f : ℂ → ℝ := fun xi => ‖c - xi‖
  have hf : Continuous f := continuous_const.sub continuous_id |>.norm
  have hnonempty : (frontier Omega.carrier).Nonempty := by
    refine ⟨Omega.boundaryParam 0, ?_⟩
    rw [← Omega.boundaryParam_range]
    exact mem_range_self 0
  obtain ⟨xiMax, hxiMax, hmax⟩ :=
    Omega.isCompact_frontier.exists_isMaxOn hnonempty hf.continuousOn
  refine ⟨delta, f xiMax, hdelta, norm_nonneg _, ?_⟩
  intro xi hxi r hr sigma hsigma
  have hdisplacement :
      ‖smoothJordanInwardPoint c xi r - xi‖ = r * ‖c - xi‖ := by
    have heq : smoothJordanInwardPoint c xi r - xi = r • (c - xi) := by
      simp only [smoothJordanInwardPoint]
      module
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos hr.1]
  rw [hdisplacement]
  calc
    delta * (r * ‖c - xi‖) = ‖c - xi‖ * (r * delta) := by ring
    _ ≤ ‖c - xi‖ * ‖sigma - smoothJordanInwardPoint c xi r‖ :=
      mul_le_mul_of_nonneg_left (hbound xi hxi r hr sigma hsigma)
        (norm_nonneg _)
    _ ≤ f xiMax * ‖sigma - smoothJordanInwardPoint c xi r‖ :=
      mul_le_mul_of_nonneg_right (hmax hxi) (norm_nonneg _)
