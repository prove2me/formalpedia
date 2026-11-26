-- Prove2me | solution 1 for intervalIntegrable_crouzeixBoundaryDoubleLayerDensity_of_integral_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:17:38.088326+00:00
-- url     : https://prove2.me/submissions/8c97685b-550b-4622-9fa7-4c9e4b5791c5

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPhaseInduction
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasure

set_option autoImplicit false
open Complex MeasureTheory Polynomial Set
open scoped ComplexConjugate Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (xi : ℂ)
    (hmass : (∫ t in (0 : ℝ)..(2 * Real.pi),
      crouzeixBoundaryDoubleLayerDensity Omega xi t) = 1) :
    IntervalIntegrable (crouzeixBoundaryDoubleLayerDensity Omega xi)
      volume 0 (2 * Real.pi) := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le Real.two_pi_pos.le]
  by_contra hnot
  have hzero : (∫ t in Ioc (0 : ℝ) (2 * Real.pi),
      crouzeixBoundaryDoubleLayerDensity Omega xi t) = 0 :=
    integral_undef hnot
  rw [intervalIntegral.integral_of_le Real.two_pi_pos.le, hzero] at hmass
  norm_num at hmass
