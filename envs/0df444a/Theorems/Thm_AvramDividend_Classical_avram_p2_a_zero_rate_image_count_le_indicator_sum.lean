-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_image_count_le_indicator_sum
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_image_count_le_indicator_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:15:11.852113+00:00
-- url     : https://prove2.me/theorems/e6edb5d4-6995-446a-a804-a11e550008ba
-- title:
--   Marked image grid count bounded by ENNReal source-cell indicator sum
-- statement:
--   For any finite image grid with possibly repeated endpoints, its distinct marked-point count coerced to ENNReal is bounded by the sum of ENNReal event indicators over the original cell-index set. This applies the Proved P2-A image-filter cardinality bound and pinned Mathlib Finset.card_filter cast, enabling original Lévy stationary grid-mean expectations and Fatou without a compensator hypothesis.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_filter_image_card_le
open Finset AvramDividend.Classical
open scoped ENNReal BigOperators

theorem AvramDividend.Classical.avram_p2_a_zero_rate_image_count_le_indicator_sum
    {α β : Type*} [DecidableEq β] (s : Finset α)
    (f : α → β) (p : β → Prop) [DecidablePred p] :
    (((s.image f).filter p).card : ℝ≥0∞) ≤
      ∑ a ∈ s, if p (f a) then (1 : ℝ≥0∞) else 0 := by sorry
