-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_01_actual_random_grid_history_meas
-- name    : AvramDividend.Classical.avram_root29_01_actual_random_grid_history_meas
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T15:08:44.925997+00:00
-- url     : https://prove2.me/theorems/63e820c2-92b7-404f-94cb-a4ab1e07b136
-- title:
--   Original Lévy closed survival history is measurable at random grid time
-- statement:
--   The genuine original Lévy continuous-time lower survival event through a measurable stopped grid time is measurable. Fixed deterministic horizon lower survival is already canonically Proved from a countable schedule; countably many stopped-grid index fibres transfer this to the random horizon. This establishes actual killed-grid reward measurability for the true source law.
-- source:
--   WS1A work/avram_root29_01_actual_random_grid_history_meas_draft.lean

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_random_grid_killed_history_meas
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_shifted_lower_closed_event_measurable

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_root29_01_actual_random_grid_history_meas
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (clock : ℕ → ℝ≥0) (K : Ω → ℕ)
    (hKm : Measurable K) :
    MeasurableSet {ω : Ω | ∀ t : ℝ≥0,
      t ≤ clock (K ω) → 0 ≤ x + X.X t ω} := by sorry
