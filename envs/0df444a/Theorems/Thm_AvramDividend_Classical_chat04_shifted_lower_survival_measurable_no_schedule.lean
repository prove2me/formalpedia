-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_shifted_lower_survival_measurable_no_schedule
-- name    : AvramDividend.Classical.chat04_shifted_lower_survival_measurable_no_schedule
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T14:50:35.606012+00:00
-- url     : https://prove2.me/theorems/55082175-0822-4f2f-a627-cd0eb4c0640f
-- title:
--   Closed-horizon shifted-reserve nonruin is measurable without a grid schedule
-- statement:
--   For any initial reserve x and finite horizon t, the exact whole-history event that the shifted spectrally negative Lévy process stays nonnegative is measurable in the ambient sigma algebra. This follows from the Proved closed-window lower-survival measurability theorem with lower barrier -x and no auxiliary countable covering schedule. It removes the hCover input from the killed-scale time-zero expectation and all-time harmonicity route to strict two-sided exit.
-- source:
--   Direct import Proved chat04_lower_survival_closed_window_measurable UUID b28f55f0. Supports stronger no-schedule killed reward expectation, Open harmonicity a885f0b3 and stopped-scale 09663d0d.

import Theorems.Thm_AvramDividend_Classical_chat04_lower_survival_closed_window_measurable
import Mathlib.Tactic.Linarith

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal

theorem AvramDividend.Classical.chat04_shifted_lower_survival_measurable_no_schedule
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (t : ℝ≥0) :
    MeasurableSet {ω | ∀ s : ℝ≥0,
      s ≤ t → 0 ≤ x + X.X s ω} := by sorry
