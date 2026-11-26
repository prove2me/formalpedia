-- Prove2me | solution 1 for integral_crouzeixBoundaryDoubleLayerDensity_complexAffine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:04:04.827978+00:00
-- url     : https://prove2.me/submissions/7eae4669-d060-47f7-8735-83cd76363f51

import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasure
import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasureAffine
import Theorems.Thm_crouzeixBoundaryDoubleLayerDensity_complexAffine

set_option autoImplicit false
open Complex MeasureTheory Set
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (a b xi : ℂ) (ha : a ≠ 0) :
    (∫ t in (0 : ℝ)..(2 * Real.pi),
      crouzeixBoundaryDoubleLayerDensity
        (Omega.complexAffine a b ha) (a * xi + b) t) =
      ∫ t in (0 : ℝ)..(2 * Real.pi),
        crouzeixBoundaryDoubleLayerDensity Omega xi t := by
  apply intervalIntegral.integral_congr
  intro t _ht
  exact crouzeixBoundaryDoubleLayerDensity_complexAffine
    Omega a b xi ha t
