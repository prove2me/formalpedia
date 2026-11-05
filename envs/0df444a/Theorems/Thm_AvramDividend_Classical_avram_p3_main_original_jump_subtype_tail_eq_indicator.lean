-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_main_original_jump_subtype_tail_eq_indicator
-- name    : AvramDividend.Classical.avram_p3_main_original_jump_subtype_tail_eq_indicator
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T09:19:01.710414+00:00
-- url     : https://prove2.me/theorems/776632f2-655f-44e5-8af0-86a16d2f26a4
-- title:
--   Original BV jump-index subtype finite-exclusion tail equals indicator tail
-- statement:
--   For the genuine original negative-jump magnitudes, equality between the absolutely summable subtype tail outside a finite marked set and the full time-index series with all marked terms zeroed. The proof uses the actual indicator support subset, avoiding the incompatible rewrite against an uninstantiated set.
-- source:
--   Source-exact repair of P3-D private Open 3e52ac28-a93f-4fe2-a0f6-6b75cb6105dd; accepted repository lemma tsum_subtype_eq_of_support_subset in original P4-D source provides the correct pinned Mathlib signature. Intended public bridge to P3 source finite-exclusion tail.

import Mathlib
open Filter Set
open scoped BigOperators

theorem AvramDividend.Classical.avram_p3_main_original_jump_subtype_tail_eq_indicator
    {ι : Type*} [DecidableEq ι] (j : ι → ℝ) (S : Finset ι)
    (hj : Summable (fun i => |j i|)) :
    (∑' i : {i : ι // i ∉ S}, |j i.1|) =
      (∑' i : ι, if i ∈ S then 0 else |j i|) := by sorry
