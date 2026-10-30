-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_01_actual_grid_hitting_index_meas
-- name    : AvramDividend.Classical.avram_root29_01_actual_grid_hitting_index_meas
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T15:07:15.34401+00:00
-- url     : https://prove2.me/theorems/8580e28d-eac7-4101-a817-f1efe77af551
-- title:
--   Genuine original-Lévy bounded two-sided grid hitting index is measurable
-- statement:
--   The actual bounded first-outside observation index K of a spectrally negative Lévy path is measurable under its exact adapted sampled filtration. The original sampled reserve forms an adapted discrete process; its two-sided outside signal is adapted; the Mathlib hittingBtwn theorem makes K a stopping time; stopping-time equality levels are measurable, and countability of Nat yields Measurable K. This discharges the random-clock continuous-history killed-event source interface.
-- source:
--   WS1A work/avram_root29_01_actual_grid_hitting_index_meas_draft.lean

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_root29_01_actual_grid_hitting_index_meas
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (clock : ℕ → ℝ≥0) (H : Filtration ℕ mΩ)
    (hH : ∀ k, H k = 𝓕 (clock k))
    (lower upper : ℝ) (m : ℕ) (K : Ω → ℕ)
    (hK : ∀ ω, K ω = hittingBtwn
      (fun k ω => max (X.X (clock k) ω - upper)
        (lower - X.X (clock k) ω)) (Set.Ioi (0 : ℝ)) 0 m ω) :
    Measurable K := by sorry
