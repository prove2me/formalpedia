-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_countable_first_candidate_cover_card_eq_dedup_sum
-- name    : AvramDividend.Classical.avram_wave7_01_countable_first_candidate_cover_card_eq_dedup_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:53:35.89129+00:00
-- url     : https://prove2.me/theorems/2880a35d-c26a-4785-9331-66cbbeba6ab6
-- title:
--   Every countable covering of jump times has exact first-occurrence ENNReal cardinal-series count
-- statement:
--   A countable (possibly duplicating) sequence of candidate jump times that covers an intrinsic set S counts S exactly by summing the indicator of first visits to S. This holds for infinite sets, so it is a correct pathwise conversion from original jump-time encard to a deduplicated measurable count without finite activity.
-- source:
--   Mathlib Nat.find first witness and minimality, Set.InjOn.encard_image, ENNReal.tsum_set_one, tsum_subtype. Genuinely useful combinatorial layer before applying Borel mark selectors to the actual source path.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_wave7_01_countable_first_candidate_cover_card_eq_dedup_sum
    (time : ℕ → ℝ≥0) (S : Set ℝ≥0)
    (hCover : S ⊆ Set.range time) :
    (S.encard : ℝ≥0∞) =
      ∑' k : ℕ,
        if time k ∈ S ∧
          (∀ j : ℕ, j < k → time j ≠ time k)
        then (1 : ℝ≥0∞) else 0 := by sorry
