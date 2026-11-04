-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_filter_card_eq_ennreal_indicator_sum
-- name    : AvramDividend.Classical.avram_p2_34dbea70_filter_card_eq_ennreal_indicator_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:12:30.813218+00:00
-- url     : https://prove2.me/theorems/9cd3c501-6f80-4b60-aa48-e52278f7949a
-- title:
--   Marked finite-grid cell cardinality equals an ENNReal indicator sum
-- statement:
--   For any finite set s and decidable marked predicate, the extended-nonnegative cardinality of s.filter marked equals the ENNReal sum of indicator terms (1 if marked, else 0). This deterministic equivalence connects the accepted grid image/cardinality bound to the exact original Lévy finite-grid expectation integrand, without integrability or any jump-rate claim.

import Mathlib

open Finset
open scoped ENNReal BigOperators

theorem AvramDividend.Classical.avram_p2_34dbea70_filter_card_eq_ennreal_indicator_sum
    {α : Type*} [DecidableEq α]
    (s : Finset α) (marked : α → Prop) [DecidablePred marked] :
    ((s.filter marked).card : ℝ≥0∞) =
      ∑ i ∈ s, (if marked i then (1 : ℝ≥0∞) else 0) := by sorry
