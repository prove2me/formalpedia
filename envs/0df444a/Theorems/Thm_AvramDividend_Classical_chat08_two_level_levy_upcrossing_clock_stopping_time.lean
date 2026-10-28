-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat08_two_level_levy_upcrossing_clock_stopping_time
-- name    : AvramDividend.Classical.chat08_two_level_levy_upcrossing_clock_stopping_time
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T08:24:25.599863+00:00
-- url     : https://prove2.me/theorems/c161d324-1ece-4b1f-80ae-df2115917fb7
-- title:
--   Adapted Lévy threshold decisions yield two-valued stopping times
-- statement:
--   A threshold decision based on the adapted Lévy process at time s defines a stopping time equal to s when the process exceeds the level and equal to the later time t otherwise. It is the first finite-valued stopping-clock case needed for stochastic regeneration.
-- source:
--   Mathlib.Probability.Process.Adapted and chat08_two_level_measurable_event_stopping_time.

import Theorems.Thm_AvramDividend_Classical_chat08_two_level_measurable_event_stopping_time
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.chat08_two_level_levy_upcrossing_clock_stopping_time
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ)
    (s t : ℝ≥0) (hst : s ≤ t) (a : ℝ) :
    IsStoppingTime ℱ
      (fun ω => if a < X.X s ω then (s : WithTop ℝ≥0)
        else (t : WithTop ℝ≥0)) := by sorry
