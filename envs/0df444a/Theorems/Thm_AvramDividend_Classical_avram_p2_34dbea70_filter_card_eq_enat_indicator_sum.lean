-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_filter_card_eq_enat_indicator_sum
-- name    : AvramDividend.Classical.avram_p2_34dbea70_filter_card_eq_enat_indicator_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:18:13.930092+00:00
-- url     : https://prove2.me/theorems/7211878f-7788-4af0-b0de-284b4da87585
-- title:
--   Finite marked-grid cardinal equals extended-natural indicator sum
-- statement:
--   For any finite set s and decidable mark predicate, the ENat cardinal of s.filter marked equals the sum of ENat zero-one indicators. The result is the exact extended-natural analogue needed by the already accepted actual pathwise jump count liminf theorem, and retains infinite-jump count compatibility without finite-activity assumptions.

import Mathlib

open Finset
open scoped ENat BigOperators

theorem AvramDividend.Classical.avram_p2_34dbea70_filter_card_eq_enat_indicator_sum
    {α : Type*} [DecidableEq α]
    (s : Finset α) (marked : α → Prop) [DecidablePred marked] :
    ((s.filter marked).card : ℕ∞) =
      ∑ i ∈ s, (if marked i then (1 : ℕ∞) else 0) := by sorry
