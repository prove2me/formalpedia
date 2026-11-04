-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_intrinsic_all_negative_marks_exhausted_by_threshold_bands
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_original_intrinsic_all_negative_marks_exhausted_by_threshold_bands
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T23:16:09.219653+00:00
-- url     : https://prove2.me/theorems/93b74ae6-8b8a-4de1-a0ec-bbb0ec6a4df2
-- title:
--   Original intrinsic negative jump count exhausts by increasing bands away from zero
-- statement:
--   For the actual spectrally negative Levy source path, the original intrinsic count of negative jumps over a time interval is the supremum of counts restricted to negative jump magnitudes at least 1/(n+1).
-- source:
--   Original intrinsic marked jump measure, previously source-accepted monotone-union helper, pinned Mathlib Archimedean reciprocal bound.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_intrinsic_marked_count_iUnion_of_monotone_bands

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_b_smalljump_original_intrinsic_all_negative_marks_exhausted_by_threshold_bands
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (ω : Ω) :
    ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ Iio (0 : ℝ)) =
    ⨆ n : ℕ,
      ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ {z : ℝ |
          z < 0 ∧ (1 : ℝ) / ((n : ℝ) + 1) ≤ -z}) := by sorry
