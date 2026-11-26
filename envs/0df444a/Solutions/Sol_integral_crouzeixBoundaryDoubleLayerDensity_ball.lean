-- Prove2me | solution 1 for integral_crouzeixBoundaryDoubleLayerDensity_ball
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:04:56.823104+00:00
-- url     : https://prove2.me/submissions/f77e667b-a4f3-4837-8f52-524c2871e686

import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasure
import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasureCircle
import Theorems.Thm_crouzeixBoundaryDoubleLayerDensity_ball_eq_inv_two_pi_of_ne
import Theorems.Thm_ae_boundaryParam_ne_of_mem_frontier
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
open Complex MeasureTheory Set
open scoped ComplexConjugate Interval Real
theorem _root_.solution
    {c xi : ℂ} {R : ℝ} (hR : 0 < R)
    (hxi : xi ∈ Metric.sphere c R) :
    (∫ t in (0 : ℝ)..(2 * Real.pi),
      crouzeixBoundaryDoubleLayerDensity
        (SmoothJordanDomain.ball c R hR) xi t) = 1 := by
  have hfrontier : xi ∈ frontier
      (SmoothJordanDomain.ball c R hR).carrier := by
    change xi ∈ frontier (Metric.ball c R)
    rw [frontier_ball c hR.ne']
    exact hxi
  calc
    (∫ t in (0 : ℝ)..(2 * Real.pi),
        crouzeixBoundaryDoubleLayerDensity
          (SmoothJordanDomain.ball c R hR) xi t) =
        ∫ _t in (0 : ℝ)..(2 * Real.pi), (2 * Real.pi)⁻¹ := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [ae_boundaryParam_ne_of_mem_frontier
        (SmoothJordanDomain.ball c R hR) hfrontier] with t ht
      intro htI
      exact
        crouzeixBoundaryDoubleLayerDensity_ball_eq_inv_two_pi_of_ne
          hR hxi t (ht htI)
    _ = 1 := by
      rw [intervalIntegral.integral_const]
      simp only [sub_zero, smul_eq_mul]
      exact mul_inv_cancel₀ (mul_ne_zero (by norm_num) Real.pi_ne_zero)
