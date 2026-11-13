-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva92_original_mapped_compensator_zero_time_supported_real_integral
-- name    : AvramDividend.Classical.avram_bva92_original_mapped_compensator_zero_time_supported_real_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T21:54:29.574767+00:00
-- url     : https://prove2.me/theorems/efd7b440-6277-48d3-aa5d-b2e1554de80c
-- title:
--   Original compensator real integral of an initial-time-supported kernel vanishes at any horizon
-- statement:
--   For the literal source mapped real Lebesgue compensator clock on [0,S] at arbitrary nonnegative S, every real integrand vanishing off time zero has zero integral. This follows from source exact BVA91 null zero atom and provides the positive-horizon compensation branch for immediate-ruin H kernels in the original BVA63 stopped source.

import Mathlib
open Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva92_original_mapped_compensator_zero_time_supported_real_integral
    (S : ℝ≥0) (f : ℝ≥0 → ℝ)
    (hSupport : ∀ t : ℝ≥0, t ≠ 0 → f t = 0) :
    (∫ t, f t
      ∂(((volume : Measure ℝ).restrict (Icc 0 (S : ℝ))).map Real.toNNReal)) = 0 := by sorry
