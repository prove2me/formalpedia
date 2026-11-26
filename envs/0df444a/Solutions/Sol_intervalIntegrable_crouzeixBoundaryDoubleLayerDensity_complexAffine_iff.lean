-- Prove2me | solution 1 for intervalIntegrable_crouzeixBoundaryDoubleLayerDensity_complexAffine_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:03:52.54274+00:00
-- url     : https://prove2.me/submissions/d0251e20-6a7c-420c-9fb5-eb978ee35e86

import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasure
import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasureAffine
import Theorems.Thm_crouzeixBoundaryDoubleLayerDensity_complexAffine

set_option autoImplicit false
open Complex MeasureTheory Set
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (a b xi : ℂ) (ha : a ≠ 0) :
    IntervalIntegrable
        (crouzeixBoundaryDoubleLayerDensity
          (Omega.complexAffine a b ha) (a * xi + b))
        volume 0 (2 * Real.pi) ↔
      IntervalIntegrable (crouzeixBoundaryDoubleLayerDensity Omega xi)
        volume 0 (2 * Real.pi) := by
  apply iff_of_eq
  congr 1
  funext t
  exact crouzeixBoundaryDoubleLayerDensity_complexAffine
    Omega a b xi ha t
