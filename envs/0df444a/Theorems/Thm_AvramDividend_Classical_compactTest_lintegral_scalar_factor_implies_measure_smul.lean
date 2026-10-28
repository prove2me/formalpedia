-- Prove2me | Theorems.Thm_AvramDividend_Classical_compactTest_lintegral_scalar_factor_implies_measure_smul
-- name    : AvramDividend.Classical.compactTest_lintegral_scalar_factor_implies_measure_smul
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T15:17:39.200601+00:00
-- url     : https://prove2.me/theorems/b629ed80-f1d2-4125-aa7f-19bcbd7ab7ae
-- title:
--   Scalar factorisation of compact test integrals determines the scaled measure
-- statement:
--   For regular locally finite Borel measures on a locally compact Hausdorff space, if all nonnegative compactly supported continuous test integrals of μ are c times those of ν, then μ is the scalar multiple c • ν.
-- source:
--   Packages the Proved compact-test lower-integral measure extensionality 4ed57fe3-78c8-4c84-926e-95e556f105d2 and Mathlib's lintegral_smul_measure into the exact Riesz bridge required to turn  finite-coordinate strong-Markov scalar integrals into a restricted pushforward law; used by 61930a38-11f1-449e-bbb6-67d59c6d5ca8.

import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.NNReal
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_measure_eq_of_compactTest_lintegral

open MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.compactTest_lintegral_scalar_factor_implies_measure_smul
    {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    [LocallyCompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {μ ν : Measure Y} (c : ℝ≥0∞)
    [μ.Regular] [(c • ν).Regular]
    [IsFiniteMeasureOnCompacts μ]
    [IsFiniteMeasureOnCompacts (c • ν)]
    (h : ∀ f : CompactlySupportedContinuousMap Y ℝ≥0,
      (∫⁻ y, ((f y : ℝ≥0) : ℝ≥0∞) ∂μ) =
      c * (∫⁻ y, ((f y : ℝ≥0) : ℝ≥0∞) ∂ν)) :
    μ = c • ν := by
  sorry
