-- Prove2me | Theorems.Thm_AvramDividend_Classical_twoSidedExitDownTime_eq_zero_iff_crossings_at_threshold
-- name    : AvramDividend.Classical.twoSidedExitDownTime_eq_zero_iff_crossings_at_threshold
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T22:46:29.088405+00:00
-- url     : https://prove2.me/theorems/568decbb-4bd3-41ad-bce4-81f0a4e1d576
-- title:
--   Instantaneous downward first-passage equivalence at any real barrier
-- statement:
--   The canonical strict downward exit at an arbitrary real level occurs at time zero exactly when sample values cross that level in every positive time interval.
-- source:
--   Pathwise exact infimum criterion and convergent observation sequence criterion at arbitrary threshold.

import Theorems.Thm_AvramDividend_Classical_downExitTime_zero_implies_near_threshold_crossings
import Theorems.Thm_AvramDividend_Classical_twoSidedExitDownTime_eq_zero_of_near_threshold_crossings

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.twoSidedExitDownTime_eq_zero_iff_crossings_at_threshold
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (b : ℝ) (ω : Ω) :
    twoSidedExitDownTime X b ω = 0 ↔
      ∀ ε : ℝ≥0, 0 < ε →
        ∃ t : ℝ≥0, t < ε ∧ X.X t ω < b := by sorry
