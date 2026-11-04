-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_intrinsic_negative_subset_threshold_exhaustion
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_original_intrinsic_negative_subset_threshold_exhaustion
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T23:34:09.680671+00:00
-- url     : https://prove2.me/theorems/e7386e2f-d6d9-416a-852a-b35290395e75
-- title:
--   Actual original negative-support marked counts exhaust by finite magnitude thresholds
-- statement:
--   The actual original Levy intrinsic jump count on any set of negative marks equals the supremum of counts on its intersection with explicit negative magnitude threshold bands 1/(n+1).
-- source:
--   Original source intrinsic marked count continuity from below, real Archimedean reciprocal inequality, actual original X.X.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_intrinsic_marked_count_iUnion_of_monotone_bands

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_b_smalljump_original_intrinsic_negative_subset_threshold_exhaustion
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (B : Set ℝ) (hNeg : B ⊆ Iio (0 : ℝ)) (ω : Ω) :
    ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ B) =
    ⨆ n : ℕ,
      ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ (B ∩ {z : ℝ |
          z < 0 ∧ (1 : ℝ) / ((n : ℝ) + 1) ≤ -z})) := by sorry
