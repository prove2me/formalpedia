-- Prove2me | Theorems.Thm_AvramDividend_Classical_realIndicator_pushforward_one_mass
-- name    : AvramDividend.Classical.realIndicator_pushforward_one_mass
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T12:22:26.03201+00:00
-- url     : https://prove2.me/theorems/772cefce-ada4-42ec-876d-2eb6794c34c9
-- title:
--   Probability mass of one under the stopped-event real-indicator pushforward law
-- statement:
--   For any measurable event A, pushforward of a measure through its real-valued zero-or-one indicator assigns to singleton {1} exactly the measure of A. This evaluates the independent stopped-past event probability in the product of its indicator law and the Lévy future-path law.
-- source:
--   Consumed with productIndicator_futureReward_lintegral_factor 7308e350-de7f-4e44-aff6-1f74bf3db945 to turn the Proved finite-grid stopped-history future-path product formula f8d196c7-e8f7-4929-bc3b-b6c523c5ea5b into a scalar event-mass times future reward expectation, ultimately leading to W-free barrier child 79978d61-9d1f-4b20-b8a5-114797a8e380.

import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.MeasurableSpace.Basic

open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.realIndicator_pushforward_one_mass
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A : Set Ω) (hA : MeasurableSet A) :
    (Measure.map (Set.indicator A (fun _ : Ω => (1 : ℝ))) P)
      ({1} : Set ℝ) = P A := by
  sorry
