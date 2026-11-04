-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_countable_mark_partition_pathwise
-- name    : AvramDividend.Classical.avram_p2_f_weighted_original_countable_mark_partition_pathwise
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T17:10:14.160865+00:00
-- url     : https://prove2.me/theorems/82724439-d896-4965-9707-cfff3aa47323
-- title:
--   Countable disjoint Borel mark partition of the original Lévy intrinsic jump measure
-- statement:
--   Every sample path of the actual original Lévy jump process has σ-additive intrinsic marked jump counts over countably many disjoint Borel mark bands on the same future interval. Extended counts may be infinite; no jump-rate identification needed.
-- source:
--   Mathlib MeasureTheory.measure_iUnion and true original count.restrict.map marked jump measure.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_f_weighted_original_countable_mark_partition_pathwise
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Countable ι]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T : ℝ≥0) (B : ι → Set ℝ)
    (hB : ∀ i, MeasurableSet (B i))
    (hDisj : Pairwise (Function.onFun Disjoint B)) :
    ∀ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ (⋃ i, B i)) =
      ∑' i, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ (B i)) := by sorry
