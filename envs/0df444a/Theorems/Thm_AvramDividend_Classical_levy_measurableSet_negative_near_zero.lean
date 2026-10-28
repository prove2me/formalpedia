-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_measurableSet_negative_near_zero
-- name    : AvramDividend.Classical.levy_measurableSet_negative_near_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T12:41:43.976843+00:00
-- url     : https://prove2.me/theorems/0612e31e-717c-4740-8f3f-ae35ed17cb3a
-- title:
--   Downward-regularity sample-path event is measurable using dense countable observations
-- statement:
--   The zero-time negative-half-line regularity event of a spectrally negative Lévy process is measurable under the process's source measurable space. The source structure guarantees each sample path right-continuous, and dense countable schedules detect every negative value. A positive cofinal sequence of horizon lengths reduces the uncountable statement to the already proved countable-path event, whose product measurability and the original whole-path measurability are also established. This supplies the measurable event needed to apply stopping-time law transfer or genuine excursion Markov identities, without claiming the event has probability one.
-- source:
--   Lévy process càdlàg path regularity and countable generating cylinders, preparatory to Rogozin and Kuznetsov-Kyprianou-Rivero excursion-height atomlessness.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_wholePath_measurable
import Theorems.Thm_AvramDividend_Classical_levy_negative_before_horizon_iff_dense_grid
import Theorems.Thm_AvramDividend_Classical_measurableSet_countable_schedule_negative_near_zero

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.levy_measurableSet_negative_near_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (times horizons : ℕ → ℝ≥0)
    (hdense : ∀ a b : ℝ≥0, a < b →
      ∃ m : ℕ, a < times m ∧ times m < b)
    (hpos : ∀ n : ℕ, 0 < horizons n)
    (hcofinal : ∀ ε : ℝ≥0, 0 < ε → ∃ n : ℕ, horizons n ≤ ε) :
    MeasurableSet
      {ω : Ω | ∀ ε : ℝ≥0, 0 < ε →
        ∃ s : ℝ≥0, s < ε ∧ X.X s ω < 0} := by sorry
