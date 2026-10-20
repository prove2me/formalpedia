-- Prove2me | Theorems.Thm_AvramDividend_Classical_measure_restrict_iUnion_eq_of_countable_directed_prefix
-- name    : AvramDividend.Classical.measure_restrict_iUnion_eq_of_countable_directed_prefix
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T14:07:40.75698+00:00
-- url     : https://prove2.me/theorems/291b7ef5-c5e2-4917-abea-fb2b803e4be8
-- title:
--   Equality of restrictions on countably directed sets extends to the union
-- statement:
--   For any countable index type, if two real Borel measures agree when restricted to every set in a directed family, they agree when restricted to the union. This is a direct pinned-Mathlib measure-theoretic lemma applicable to the rational strict pre-ruin cover of dividend-payment times, whose index is countable and directed but not naturally enumerated as an increasing ℕ-sequence.
-- source:
--   Pinned Mathlib.MeasureTheory.Measure.restrict_iUnion_apply_eq_iSup; bridge for Avram et al. 2007 discounted dividends.

import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
open MeasureTheory Set

theorem AvramDividend.Classical.measure_restrict_iUnion_eq_of_countable_directed_prefix
    {ι : Type*} [Countable ι]
    (μ ν : Measure ℝ) (s : ι → Set ℝ)
    (hd : Directed (· ⊆ ·) s)
    (heq : ∀ i, μ.restrict (s i) = ν.restrict (s i)) :
    μ.restrict (⋃ i, s i) = ν.restrict (⋃ i, s i) := by sorry
