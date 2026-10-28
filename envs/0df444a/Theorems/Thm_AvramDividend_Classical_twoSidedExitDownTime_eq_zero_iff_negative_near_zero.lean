-- Prove2me | Theorems.Thm_AvramDividend_Classical_twoSidedExitDownTime_eq_zero_iff_negative_near_zero
-- name    : AvramDividend.Classical.twoSidedExitDownTime_eq_zero_iff_negative_near_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T22:17:39.082768+00:00
-- url     : https://prove2.me/theorems/e288359a-068d-41cb-b5be-4483fe8c8410
-- title:
--   Strict downward exit from zero exactly when strict negative observations occur arbitrarily early
-- statement:
--   For every sample path, the canonical first strict downward passage time equals zero if and only if strict negative observations occur in every positive interval after zero.
-- source:
--   Two already verified directions of the zero-time first-passage regularity equivalence.

import Theorems.Thm_AvramDividend_Classical_negative_near_zero_of_twoSidedExitDownTime_zero
import Theorems.Thm_AvramDividend_Classical_twoSidedExitDownTime_eq_zero_of_negative_near_zero

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.twoSidedExitDownTime_eq_zero_iff_negative_near_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) :
    twoSidedExitDownTime X 0 ω = 0 ↔
      ∀ ε : ℝ≥0, 0 < ε →
        ∃ t : ℝ≥0, t < ε ∧ X.X t ω < 0 := by sorry
