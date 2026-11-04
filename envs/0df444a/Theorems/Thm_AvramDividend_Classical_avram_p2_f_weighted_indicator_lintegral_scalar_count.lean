-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_indicator_lintegral_scalar_count
-- name    : AvramDividend.Classical.avram_p2_f_weighted_indicator_lintegral_scalar_count
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T13:26:53.886742+00:00
-- url     : https://prove2.me/theorems/ed41dfad-c539-4035-a879-b123cc442c25
-- title:
--   Measurable-cell indicator integrates to constant ENNReal weight times its mass
-- statement:
--   For any genuine measure on a measurable space and any measurable marked cell S, the integral of the pointwise indicator of S with constant nonnegative ENNReal weight c equals c multiplied by the actual measure μ(S). This remains exact when c=0 or c=∞, and is the deterministic pathwise bridge from predictable jump integrands to source marked jump counts.
-- source:
--   Pinned Mathlib MeasureTheory.lintegral_indicator, lintegral_const and ENNReal multiplication.

import Mathlib

open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.avram_p2_f_weighted_indicator_lintegral_scalar_count
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (S : Set α)
    (hS : MeasurableSet S) (c : ℝ≥0∞) :
    (∫⁻ x, S.indicator (fun _ => c) x ∂μ) = c * μ S := by sorry
