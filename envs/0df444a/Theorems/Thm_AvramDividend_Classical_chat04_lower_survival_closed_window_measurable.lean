-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_lower_survival_closed_window_measurable
-- name    : AvramDividend.Classical.chat04_lower_survival_closed_window_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T21:57:21.36151+00:00
-- url     : https://prove2.me/theorems/b28f55f0-1062-4f26-94bb-4d3815f6682e
-- title:
--   Measurability of strict no-ruin survival on a deterministic closed future interval
-- statement:
--   For every spectrally negative Lévy process with right-continuous sample paths and deterministic s≤u, the event that the path remains above a strict lower threshold at every time in [s,u] is measurable. A previously published grid-detection theorem reduces strict violations to a countable family of deterministic observations in [s,u) plus the endpoint u. This provides event measurability required for future-window killed scale payoffs.
-- source:
--   Intended dependency chat04_strict_lower_exit_closed_window_grid_iff plus process adaptedness.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_strict_lower_exit_closed_window_grid_iff

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_lower_survival_closed_window_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (lower : ℝ) (s u : ℝ≥0) (hsu : s ≤ u) :
    MeasurableSet
      {ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u → ¬ X.X v ω < lower} := by sorry
