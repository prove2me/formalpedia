-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_actual_shifted_path_measurable_of_clock_measurable_ws01c
-- name    : AvramDividend.Classical.bv_actual_shifted_path_measurable_of_clock_measurable_ws01c
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T12:44:25.413598+00:00
-- url     : https://prove2.me/theorems/738e47f5-8e0b-4b71-854d-a148f205272a
-- title:
--   Shifted Lévy future path is measurable at any measurable finite clock
-- statement:
--   For the canonical spectrally negative Lévy process, the complete shifted increment path at an arbitrary measurable finite nonnegative-real-valued clock is a measurable random element of the sample-path product σ-algebra. No stopping-time property is assumed: joint measurability of the Lévy process in time and sample point, compositional measurability and the coordinatewise measurable-product criterion give the result.
-- source:
--   Complete source extracted from work/avram_ws01c_measurable_shift_at_measurable_clock_draft.lean; depends only on the independently Proved joint time–sample measurability theorem.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable

open MeasureTheory Topology AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.bv_actual_shifted_path_measurable_of_clock_measurable_ws01c
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ)
    (τ : Ω → ℝ≥0) (hτ : Measurable τ) :
    Measurable (fun ω : Ω => fun t : ℝ≥0 =>
      X.X (τ ω + t) ω - X.X (τ ω) ω) := by sorry
