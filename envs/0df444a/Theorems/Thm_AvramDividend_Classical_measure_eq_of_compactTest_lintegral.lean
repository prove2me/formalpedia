-- Prove2me | Theorems.Thm_AvramDividend_Classical_measure_eq_of_compactTest_lintegral
-- name    : AvramDividend.Classical.measure_eq_of_compactTest_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T14:41:38.286563+00:00
-- url     : https://prove2.me/theorems/4ed57fe3-78c8-4c84-926e-95e556f105d2
-- title:
--   Uniqueness of regular measures from compact continuous nonnegative lower-integral tests
-- statement:
--   Two regular locally finite measures on a locally compact Hausdorff space coincide if the lower integrals of every compactly supported continuous nonnegative test function coincide. Converts strong-Markov continuous cylinder reward integrals into finite-dimensional distribution equality.
-- source:
--   General Riesz–Markov measure-uniqueness bridge needed to turn the canonical finite-stopping scalar strong-Markov reward result into equality of finite-coordinate shifted path laws, then into canonical full path independence theorem 61930a38-11f1-449e-bbb6-67d59c6d5ca8.

import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.NNReal
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.measure_eq_of_compactTest_lintegral
    {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    [LocallyCompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {μ ν : Measure Y} [μ.Regular] [ν.Regular]
    [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
    (h : ∀ f : CompactlySupportedContinuousMap Y ℝ≥0,
      (∫⁻ y, ((f y : ℝ≥0) : ℝ≥0∞) ∂μ) =
      (∫⁻ y, ((f y : ℝ≥0) : ℝ≥0∞) ∂ν)) :
    μ = ν := by
  sorry
