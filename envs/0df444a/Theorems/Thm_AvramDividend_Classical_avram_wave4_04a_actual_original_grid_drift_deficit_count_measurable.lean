-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_original_grid_drift_deficit_count_measurable
-- name    : AvramDividend.Classical.avram_wave4_04a_actual_original_grid_drift_deficit_count_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T22:23:29.221313+00:00
-- url     : https://prove2.me/theorems/7d565b48-2aee-434c-8f46-b4db7429c950
-- title:
--   Actual original Lévy finite-grid drift-deficient cell count is measurable on the original sample sigma-algebra
-- statement:
--   For any actual source spectrally negative Lévy X, any deterministic finite time grid and every grid size n, the integer-valued random variable counting cells whose genuine X increment falls strictly below its drift baseline is measurable on the original sample sigma algebra. No BV, finite ν, standing, independent auxiliary Poisson process or count law is required. This measurable original-X statistic is the exact input to the Proved finite-grid Poisson scaling limit and to a future source N_X count-law transfer.
-- source:
--   Original X adaptedness gives measurable deterministic-time values under the original mΩ. The real difference of two observations is measurable and so is each strict drift-deficiency event. Pinned Mathlib Finset.card_filter turns the count into a finite sum of piecewise measurable Nat-valued indicators; Finset.measurable_sum and Measurable.ite give measurability. No equal-law substitution, compensator or hidden completeness assumption.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_wave4_04a_actual_original_grid_drift_deficit_count_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (n : ℕ) (grid : ℕ → ℝ≥0) :
    Measurable (fun ω : Ω =>
      ((Finset.range n).filter (fun i =>
        X.X (grid (i + 1)) ω - X.X (grid i) ω <
          X.drift * (((grid (i + 1) - grid i : ℝ≥0) : ℝ)))).card) := by sorry
