-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat06_count_measurable_from_arrival_threshold
-- name    : AvramDividend.Classical.chat06_count_measurable_from_arrival_threshold
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T07:24:51.748312+00:00
-- url     : https://prove2.me/theorems/bf0c187e-b57e-4677-b3f3-2ae2d64dd524
-- title:
--   Renewal count is measurable directly from its arrival-threshold equivalence
-- statement:
--   The measurable interarrival variables and exact pathwise equivalence between exceeding any renewal count level and an arrival-time partial sum at the clock imply measurability of the count at that clock. For each n, the event N(clock)≤n equals the measurable event that the next finite arrival sum exceeds the clock. The proof applies Mathlib's measurable_of_Iic criterion. It removes an unnecessary standalone count-measurability assumption from future IID natural-filtration factorisation lemmas.
-- source:
--   bv_count_measurable_from_arrival_threshold_chat06_20261022.lean, 28 lines, 1002 bytes, SHA-256 9570b65cae208002bea573e445de11c4a25b9946b7d3d35d79a3a37029fd74ce; remote probe f4d2f9be-0847-48e5-95ad-f7eb3f73645e reached sentinel with no source errors.

import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Pi

open MeasureTheory Set
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem AvramDividend.Classical.chat06_count_measurable_from_arrival_threshold
    {Ω : Type*} [MeasurableSpace Ω]
    (τ : ℕ → Ω → ℝ)
    (hτ : ∀ i, Measurable (τ i))
    (N : Ω → ℝ → ℕ)
    (hThreshold : ∀ ω u k,
      k < N ω u ↔ (∑ i ∈ Finset.range (k + 1), τ i ω) ≤ u)
    (clock : ℝ) :
    Measurable (fun ω => N ω clock) := by sorry
