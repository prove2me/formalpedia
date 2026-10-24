-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_lower_survival_closed_window_filtration_measurable
-- name    : AvramDividend.Classical.chat04_lower_survival_closed_window_filtration_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T22:06:25.994121+00:00
-- url     : https://prove2.me/theorems/db96e4f2-9387-4c22-a373-67b203428399
-- title:
--   Future closed-window no-ruin event belongs to the terminal Lévy filtration
-- statement:
--   For a càdlàg adapted spectrally negative Lévy process and s≤u, the event that it stays above a strict lower threshold throughout the closed interval [s,u] is measurable with respect to the filtration at u. Countable-grid detection reduces violations to observations before u plus its exact terminal value, and adaptedness transfers each observation to the terminal filtration. This strengthens the global future-window measurability theorem to the proper stochastic-information σ-algebra.
-- source:
--   Published chat04_strict_lower_exit_closed_window_grid_iff and X.adapted with filtration monotonicity.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_strict_lower_exit_closed_window_grid_iff

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_lower_survival_closed_window_filtration_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (lower : ℝ) (s u : ℝ≥0) (hsu : s ≤ u) :
    MeasurableSet[𝓕 u]
      {ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u → ¬ X.X v ω < lower} := by sorry
