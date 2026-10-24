-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat08_levy_upcrossing_event_measurable_at_time
-- name    : AvramDividend.Classical.chat08_levy_upcrossing_event_measurable_at_time
-- status  : Open
-- author  : @WillR
-- created : 2026-10-23T23:43:18.015783+00:00
-- url     : https://prove2.me/theorems/bb9f53a4-021a-40c6-b4e1-6b00e03ab3cd
-- title:
--   Lévy strict upcrossing at a deterministic time is observable in the filtration
-- statement:
--   The adapted spectrally negative Lévy process has an observable value at every deterministic time. Consequently its strict threshold upcrossing event at that time is measurable in the corresponding filtration σ-algebra.
-- source:
--   Mathlib.Probability.Process.Adapted and SpectrallyNegativeLevy.adapted.

import Mathlib.Probability.Process.Adapted
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat08_levy_upcrossing_event_measurable_at_time
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) (s : ℝ≥0) (a : ℝ) :
    MeasurableSet[ℱ s] {ω | a < X.X s ω} := by sorry
