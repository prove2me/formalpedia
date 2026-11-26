-- Prove2me | solution 1 for exists_inward_boundary_cross_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:48:06.473443+00:00
-- url     : https://prove2.me/submissions/d150b4cc-abad-4127-8be0-d898550732ad

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Theorems.Thm_exists_inward_boundary_denominator_bound
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
    (Omega : SmoothJordanDomain) {c xi : ℂ}
    (hc : c ∈ Omega.carrier) (hxi : xi ∈ frontier Omega.carrier) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ r ∈ Ioc (0 : ℝ) 1, ∀ sigma ∈ frontier Omega.carrier,
        delta * ‖smoothJordanInwardPoint c xi r - xi‖ ≤
          ‖c - xi‖ * ‖sigma - smoothJordanInwardPoint c xi r‖ := by
  obtain ⟨delta, hdelta, hbound⟩ :=
    exists_inward_boundary_denominator_bound Omega hc hxi
  refine ⟨delta, hdelta, ?_⟩
  intro r hr sigma hsigma
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
      mul_le_mul_of_nonneg_left (hbound r hr sigma hsigma)
        (norm_nonneg _)
