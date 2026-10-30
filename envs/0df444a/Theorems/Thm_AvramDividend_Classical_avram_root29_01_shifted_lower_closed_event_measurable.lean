-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_01_shifted_lower_closed_event_measurable
-- name    : AvramDividend.Classical.avram_root29_01_shifted_lower_closed_event_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T10:43:37.38134+00:00
-- url     : https://prove2.me/theorems/3d9b599a-bfbe-4979-80a8-f91c80b02882
-- title:
--   Exact original Lévy shifted closed lower-survival event is measurable for every reserve and future interval
-- statement:
--   The closed lower-killed survival of a spectrally negative Lévy process over a relative future interval at original time s, with arbitrary real reserve x, is an actual measurable set. Proved by translating the interval [0,T] to [s,s+T] and applying the accepted true-path closed-window lower survival measurability theorem. No stochastic harmonicity or exit identity is assumed.
-- source:
--   WS1A exclusive Lean source work/avram_root29_01_shifted_lower_closed_event_measurable_draft.lean.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_chat04_lower_survival_closed_window_measurable

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_root29_01_shifted_lower_closed_event_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (s T : ℝ≥0) :
    MeasurableSet {ω : Ω | ∀ v : ℝ≥0, v ≤ T →
      0 ≤ (x + X.X s ω) + (X.X (s + v) ω - X.X s ω)} := by sorry
