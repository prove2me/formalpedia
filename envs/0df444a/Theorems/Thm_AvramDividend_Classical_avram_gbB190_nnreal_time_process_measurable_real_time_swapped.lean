-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB190_nnreal_time_process_measurable_real_time_swapped
-- name    : AvramDividend.Classical.avram_gbB190_nnreal_time_process_measurable_real_time_swapped
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T19:12:40.624892+00:00
-- url     : https://prove2.me/theorems/89cf17f0-1cd3-4190-ba7b-aaec5c7c0e48
-- title:
--   Swap path/time coordinates and clamp real time to NNReal in a measurable process
-- statement:
--   Pass jointly measurable nonnegative-time process f(s,omega) to the real-time and path-swapped map f(toNNReal(t),omega). This is the deterministic measurability bridge from original postpayment reserve to B188 and B187.

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB190_nnreal_time_process_measurable_real_time_swapped
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (f : ℝ≥0 → Ω → ℝ)
    (hf : Measurable (fun z : ℝ≥0 × Ω => f z.1 z.2)) :
    Measurable (fun z : Ω × ℝ =>
      f (Real.toNNReal z.2) z.1) := by sorry
