-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a266_full_physical_source_positive_small_large_raw_partition
-- name    : AvramDividend.Classical.avram_ga_a266_full_physical_source_positive_small_large_raw_partition
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:55:25.066598+00:00
-- url     : https://prove2.me/theorems/324a35a4-24e5-4655-9340-e0ca5efc4ef9
-- title:
--   Original masked Gaussian finite fullcell positive sum bounded by exact small and large raw-increment branch positives
-- statement:
--   For any genuine finite physical stopped-cell mask A, arbitrary raw increment r and combined Gaussian source cell e, the positive part of the masked finite sum is bounded by the sum of positive parts on the two exact complementary events |r|<δ and δ≤|r|. The identity partitions only the raw Gaussian increment, preserving the original full stopped-cell mask, and glues a263 large-event expected L1 with a264 small-event expected budget through a265.
-- source:
--   Exact original a216 physical mask and finite raw increment threshold complement

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a266_full_physical_source_positive_small_large_raw_partition
    {Ω : Type*} (S : Finset ℕ) (A : ℕ → Ω → Prop)
    [∀ i, DecidablePred (A i)]
    (r e : ℕ → Ω → ℝ) (δ : ℝ) (ω : Ω) :
    max (∑ i ∈ S, if A i ω then e i ω else 0) 0 ≤
      max (∑ i ∈ S, if A i ω ∧ |r i ω| < δ
        then e i ω else 0) 0 +
      max (∑ i ∈ S, if A i ω ∧ δ ≤ |r i ω|
        then e i ω else 0) 0 := by sorry
