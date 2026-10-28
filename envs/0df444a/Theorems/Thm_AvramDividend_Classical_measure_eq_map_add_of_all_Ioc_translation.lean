-- Prove2me | Theorems.Thm_AvramDividend_Classical_measure_eq_map_add_of_all_Ioc_translation
-- name    : AvramDividend.Classical.measure_eq_map_add_of_all_Ioc_translation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T18:01:26.36798+00:00
-- url     : https://prove2.me/theorems/0292e86b-89d2-41f5-931d-cf66e08f4b38
-- title:
--   Stieltjes interval-mass translation determines the pushforward measure
-- statement:
--   If a locally finite Borel measure assigns translated intervals exactly the masses given by a second measure on the original intervals, then the first measure is the pushforward of the second under translation. Needed to upgrade the proven barrier dividend Stieltjes interval identities to equality of discounted future payoff integrals.
-- source:
--   Genuine measure-theoretic intermediate for strong-Markov barrier value child 79978d61-9d1f-4b20-b8a5-114797a8e380: follow interval identities 788f2fa3-ed75-4f21-9602-339f7386961a by support and increment arguments to obtain hshift, then use this lemma and Mathlib lintegral_map for weighted dividend reward equality. No W assumptions.

import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.measure_eq_map_add_of_all_Ioc_translation
    (μ ν : Measure ℝ) [IsLocallyFiniteMeasure μ]
    (u : ℝ)
    (hshift : ∀ a b : ℝ, a < b →
      μ (Set.Ioc (u + a) (u + b)) = ν (Set.Ioc a b)) :
    μ = Measure.map (fun t : ℝ => u + t) ν := by
  sorry
