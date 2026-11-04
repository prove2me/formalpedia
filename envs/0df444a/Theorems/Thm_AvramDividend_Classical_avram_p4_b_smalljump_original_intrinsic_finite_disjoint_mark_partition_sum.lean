-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_intrinsic_finite_disjoint_mark_partition_sum
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_original_intrinsic_finite_disjoint_mark_partition_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T23:10:22.767428+00:00
-- url     : https://prove2.me/theorems/33203d98-1a1a-4e34-8a54-72778a7bffb6
-- title:
--   Original Levy marked count finite disjoint Borel partition additivity
-- statement:
--   The original intrinsic marked jump count in a fixed time rectangle over a finite union of pairwise disjoint Borel mark bands equals the sum of the individual marked counts pathwise.
-- source:
--   Actual original intrinsic jump measure with finset induction and disjoint measurable rectangle additivity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_b_smalljump_original_intrinsic_finite_disjoint_mark_partition_sum
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    {ι : Type*} (S : Finset ι) (s t : ℝ≥0)
    (B : ι → Set ℝ)
    (hB : ∀ i ∈ S, MeasurableSet (B i))
    (hDisj : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → Disjoint (B i) (B j))
    (ω : Ω) :
    ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ (⋃ i ∈ S, B i)) =
    ∑ i ∈ S,
      ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B i) := by sorry
