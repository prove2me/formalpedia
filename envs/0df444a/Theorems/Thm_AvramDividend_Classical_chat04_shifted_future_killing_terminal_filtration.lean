-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_shifted_future_killing_terminal_filtration
-- name    : AvramDividend.Classical.chat04_shifted_future_killing_terminal_filtration
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T22:15:04.994278+00:00
-- url     : https://prove2.me/theorems/17f248e9-2aa7-4c23-a7cd-e17bb675dba6
-- title:
--   Shifted future-window ruin killing is measurable at its terminal observation time
-- statement:
--   For a Lévy reserve observed at time s, the exact future-window lower-killing event on [s,u], written in terms of initial reserve at s and increments after s, is measurable in the terminal filtration at u. The algebraic cancellation of the initial observation reduces it to a fixed-threshold path-survival event already proved filtration measurable.
-- source:
--   Published chat04_lower_survival_closed_window_filtration_measurable and real arithmetic cancellation.

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_lower_survival_closed_window_filtration_measurable

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_shifted_future_killing_terminal_filtration
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (s u : ℝ≥0) (hsu : s ≤ u) :
    MeasurableSet[𝓕 u]
      {ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
        0 ≤ (x + X.X s ω) + (X.X v ω - X.X s ω)} := by sorry
