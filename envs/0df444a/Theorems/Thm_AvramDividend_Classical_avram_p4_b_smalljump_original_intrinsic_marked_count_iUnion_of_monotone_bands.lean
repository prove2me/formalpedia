-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_intrinsic_marked_count_iUnion_of_monotone_bands
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_original_intrinsic_marked_count_iUnion_of_monotone_bands
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T23:04:47.87421+00:00
-- url     : https://prove2.me/theorems/eee185f4-1808-499a-a403-3d0f7285810f
-- title:
--   Original Levy marked jump count is continuous from below on increasing mark bands
-- statement:
--   The original spectrally negative Levy process intrinsic jump count over a fixed physical time rectangle and an increasing union of marked bands equals the supremum of the counts over the individual bands, pathwise.
-- source:
--   Exact original intrinsic marked jump measure and pinned Mathlib Monotone.measure_iUnion continuity from below.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_b_smalljump_original_intrinsic_marked_count_iUnion_of_monotone_bands
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (B : ℕ → Set ℝ) (hB : Monotone B) (ω : Ω) :
    ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ (⋃ n, B n)) =
    ⨆ n, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ B n) := by sorry
