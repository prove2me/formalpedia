-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_intrinsic_marked_count_union_subadditive
-- name    : AvramDividend.Classical.avram_wave7_06_original_intrinsic_marked_count_union_subadditive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T15:30:00.999864+00:00
-- url     : https://prove2.me/theorems/ae5fdadb-6a10-4c23-b5f5-7d835f1cc755
-- title:
--   Original intrinsic marked counts are subadditive across arbitrary mark unions
-- statement:
--   For the genuine pathwise jump measure NX ω and any mark sets B and C, the count on their union during (0,T] is at most the sum of the individual counts. This is an unconditional outer-measure bound on original jump marks and supports marked grid partition estimates.
-- source:
--   Original-source marked measure combinatorics for compensated marked-cell estimates, no auxiliary process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_intrinsic_marked_count_union_subadditive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (T : ℝ≥0) (B C : Set ℝ) :
    (let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
     NX ω (Ioc 0 T ×ˢ (B ∪ C)) ≤
     NX ω (Ioc 0 T ×ˢ B) + NX ω (Ioc 0 T ×ˢ C)) := by sorry
