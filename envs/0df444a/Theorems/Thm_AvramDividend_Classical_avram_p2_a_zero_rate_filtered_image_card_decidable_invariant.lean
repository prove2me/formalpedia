-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_filtered_image_card_decidable_invariant
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_filtered_image_card_decidable_invariant
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T15:32:34.261984+00:00
-- url     : https://prove2.me/theorems/6f21d82e-cd3c-4f72-ba0a-377d1a954072
-- title:
--   Filtered finite grid cardinality invariant under endpoint decidable equality
-- statement:
--   Using the Proved Finset.image DecidableEq invariance theorem, prove that applying the same decidable mark filter and taking cardinality is independent of the endpoint equality-decider implementation. This is the exact interface in original Levy marked uniform-grid Fatou proofs with two imported mesh lemmas.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_finset_image_decidable_invariant

open Finset AvramDividend.Classical

theorem AvramDividend.Classical.avram_p2_a_zero_rate_filtered_image_card_decidable_invariant
    {α β : Type*} (s : Finset α) (f : α → β) (p : β → Prop)
    [DecidablePred p] (d₁ d₂ : DecidableEq β) :
    ((@Finset.image α β d₁ f s).filter p).card =
      ((@Finset.image α β d₂ f s).filter p).card := by sorry
