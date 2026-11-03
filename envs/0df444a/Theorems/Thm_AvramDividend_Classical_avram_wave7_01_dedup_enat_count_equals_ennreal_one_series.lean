-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_dedup_enat_count_equals_ennreal_one_series
-- name    : AvramDividend.Classical.avram_wave7_01_dedup_enat_count_equals_ennreal_one_series
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:52:06.505413+00:00
-- url     : https://prove2.me/theorems/40b220ef-39ee-4dec-bfd6-686fe92853a6
-- title:
--   Every injection of countably active jump candidates has exact extended-cardinal indicator-series count
-- statement:
--   For any countable family of actual candidate jump times, if no two active indices select the same time, the number (possibly infinite) of distinct active times is exactly the nonnegative extended sum of their activity indicators. This converts the pathwise deduplicated time enumeration into the same ENNReal count used by the original source Lévy jump compensator, without finite activity.
-- source:
--   Formal cardinality transport Set.InjOn.encard_image, exact ENNReal.tsum_set_one, and tsum_subtype in pinned Mathlib; deterministic combinatorial lemma applicable to raw source paths.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_wave7_01_dedup_enat_count_equals_ennreal_one_series
    (time : ℕ → ℝ≥0) (A : Set ℕ)
    (hInj : Set.InjOn time A) :
    ((time '' A).encard : ℝ≥0∞) =
      ∑' k : ℕ, if k ∈ A then (1 : ℝ≥0∞) else 0 := by sorry
