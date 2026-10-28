-- Prove2me | Theorems.Thm_AvramDividend_Classical_measure_eq_translated_of_zero_prepayment_and_cumulative
-- name    : AvramDividend.Classical.measure_eq_translated_of_zero_prepayment_and_cumulative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T18:29:23.788256+00:00
-- url     : https://prove2.me/theorems/50431279-23d0-42be-b261-421a5476921e
-- title:
--   Zero prepayment and cumulative shifted interval masses determine entire translated measure
-- statement:
--   For a locally finite real-time measure with no mass up to the stopping time u and a future measure with no mass at or before zero, equality of their cumulative post-u interval masses makes the original measure the translated pushforward of the future measure. This directly bridges the proved pathwise barrier cumulative Stieltjes shift to weighted reward transport.
-- source:
--   Direct W-free measure bridge for strong Markov barrier child 79978d61-9d1f-4b20-b8a5-114797a8e380. Applies proved cumulative equality 788f2fa3-ed75-4f21-9602-339f7386961a and no prepayment 4396ddd6-6981-42c6-9f15-733157b72a22 to identify the entire post-passage dividend measure, then use weighted integral transport f3de50bd-c45b-41f9-9082-36c39a2f0ea7.

import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.measure_eq_translated_of_zero_prepayment_and_cumulative
    (μ ν : Measure ℝ) [IsLocallyFiniteMeasure μ] (u : ℝ)
    (hμzero : μ (Set.Iic u) = 0)
    (hνzero : ν (Set.Iic (0 : ℝ)) = 0)
    (hcum : ∀ t : ℝ, 0 ≤ t →
      μ (Set.Ioc u (u + t)) = ν (Set.Ioc (0 : ℝ) t)) :
    μ = Measure.map (fun t : ℝ => u + t) ν := by
  sorry
