-- Prove2me | solution 1 for crouzeixBoundaryPhaseContractive_ball_of_boundaryDoubleLayerDensity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:35:40.029699+00:00
-- url     : https://prove2.me/submissions/d0f457cd-2271-4f49-beeb-b37afe1eaef6

import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasure
import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasureCircle
import Theorems.Thm_integral_crouzeixBoundaryDoubleLayerDensity_ball
import Theorems.Thm_crouzeixBoundaryDoubleLayerDensity_ball_nonneg
import Theorems.Thm_crouzeixBoundaryPhaseContractive_of_boundaryDoubleLayerDensity
import Theorems.Thm_intervalIntegrable_crouzeixBoundaryDoubleLayerDensity_of_integral_eq_one


set_option autoImplicit false
open Complex MeasureTheory Set
open scoped ComplexConjugate Interval Real
theorem _root_.solution
    {c : ℂ} {R : ℝ} (hR : 0 < R) (p : Polynomial ℂ) :
    CrouzeixBoundaryPhaseContractive
      (SmoothJordanDomain.ball c R hR) p := by
  apply crouzeixBoundaryPhaseContractive_of_boundaryDoubleLayerDensity
  · intro xi hxi
    apply
      intervalIntegrable_crouzeixBoundaryDoubleLayerDensity_of_integral_eq_one
    apply integral_crouzeixBoundaryDoubleLayerDensity_ball hR
    change xi ∈ frontier (Metric.ball c R) at hxi
    rwa [frontier_ball c hR.ne'] at hxi
  · intro xi hxi
    apply integral_crouzeixBoundaryDoubleLayerDensity_ball hR
    change xi ∈ frontier (Metric.ball c R) at hxi
    rwa [frontier_ball c hR.ne'] at hxi
  · intro xi hxi t _ht
    apply crouzeixBoundaryDoubleLayerDensity_ball_nonneg hR
    change xi ∈ frontier (Metric.ball c R) at hxi
    rwa [frontier_ball c hR.ne'] at hxi
