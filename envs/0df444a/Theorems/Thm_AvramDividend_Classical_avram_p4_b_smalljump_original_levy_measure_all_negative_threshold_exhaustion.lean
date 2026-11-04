-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_levy_measure_all_negative_threshold_exhaustion
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_original_levy_measure_all_negative_threshold_exhaustion
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T23:36:51.91274+00:00
-- url     : https://prove2.me/theorems/92d227f5-9052-4eb2-a967-46c74a892826
-- title:
--   Original Levy intensity on negative marks exhausts by increasing magnitude cutoffs
-- statement:
--   The original source Levy jump intensity over all negative marks equals the supremum of intensities of negative marks with magnitude at least 1/(n+1).
-- source:
--   Original X.nu and pinned Mathlib monotone measure continuity from below; Archimedean reciprocal cutoff.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_b_smalljump_original_levy_measure_all_negative_threshold_exhaustion
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    X.ν (Iio (0 : ℝ)) =
      ⨆ n : ℕ, X.ν {z : ℝ |
        z < 0 ∧ (1 : ℝ) / ((n : ℝ) + 1) ≤ -z} := by sorry
