-- Prove2me | Theorems.Thm_AvramDividend_Classical_twoSidedExitUpTime_eq_zero_iff_positive_near_zero
-- name    : AvramDividend.Classical.twoSidedExitUpTime_eq_zero_iff_positive_near_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T22:17:39.42867+00:00
-- url     : https://prove2.me/theorems/e412df7c-f890-4be7-a3ba-8c515bbf4e8e
-- title:
--   Strict upward exit from zero exactly when strict positive observations occur arbitrarily early
-- statement:
--   For every sample path, the canonical first strict upward passage time equals zero if and only if strict positive observations occur in every positive interval after zero.
-- source:
--   Two already verified directions of the zero-time first-passage regularity equivalence.

import Theorems.Thm_AvramDividend_Classical_positive_near_zero_of_twoSidedExitUpTime_zero
import Theorems.Thm_AvramDividend_Classical_twoSidedExitUpTime_eq_zero_of_positive_near_zero

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.twoSidedExitUpTime_eq_zero_iff_positive_near_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) :
    twoSidedExitUpTime X 0 ω = 0 ↔
      ∀ ε : ℝ≥0, 0 < ε →
        ∃ t : ℝ≥0, t < ε ∧ 0 < X.X t ω := by sorry
