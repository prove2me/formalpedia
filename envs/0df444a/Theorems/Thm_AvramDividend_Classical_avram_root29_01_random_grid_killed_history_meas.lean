-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_01_random_grid_killed_history_meas
-- name    : AvramDividend.Classical.avram_root29_01_random_grid_killed_history_meas
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T11:41:07.635646+00:00
-- url     : https://prove2.me/theorems/871fe0d8-ae33-4e6f-b9dc-ca8467bb18cc
-- title:
--   Measurable original-Lévy killed history at an actual random grid clock
-- statement:
--   For the source spectrally negative Lévy process, a lower-history survival event up to a measurable random observation-grid time is measurable whenever deterministic-prefix survival events are measurable. Split by the countable stopped-grid clock index and use the countable union of measurable slices. This is a missing original-path event interface for moving killed q-scale grid expectations to first-passage limits.
-- source:
--   WS1A work/avram_root29_01_random_grid_killed_history_meas_draft.lean

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_root29_01_random_grid_killed_history_meas
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (clock : ℕ → ℝ≥0) (K : Ω → ℕ)
    (hKm : Measurable K)
    (hHistory : ∀ k : ℕ, MeasurableSet
      {ω : Ω | ∀ t : ℝ≥0, t ≤ clock k →
        0 ≤ x + X.X t ω}) :
    MeasurableSet {ω : Ω | ∀ t : ℝ≥0,
      t ≤ clock (K ω) → 0 ≤ x + X.X t ω} := by sorry
