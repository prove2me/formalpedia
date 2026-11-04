-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_uniform_grid_probability_sum
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_uniform_grid_probability_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:51:08.31921+00:00
-- url     : https://prove2.me/theorems/650af6c4-f9e5-49e2-bf6e-e185452bd291
-- title:
--   Original Lévy stationary uniform-grid mean collapses to cell count times one genuine source probability
-- statement:
--   On the original sample space, every uniform time-cell duration equals δ=T/(n+1); therefore the finite sum of source one-time marked cell probabilities equals (n+1) times the original source one-time event probability at δ, in ENNReal and including zero horizon or infinite measures. This is a deterministic consequence of exact source-cell width.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_uniform_cell_width

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p2_a_zero_rate_uniform_grid_probability_sum
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (n : ℕ) (B : Set ℝ) :
    (∑ j ∈ Finset.range (n + 1),
      P {ω : Ω | X.X (((((j + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) -
        ((j : ℝ≥0) * (T / ((n : ℝ≥0) + 1))))) ω ∈ B}) =
    (((n + 1 : ℕ) : ℝ≥0∞) * P {ω : Ω | X.X (T / ((n : ℝ≥0) + 1)) ω ∈ B}) := by sorry
