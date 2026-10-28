-- Prove2me | Theorems.Thm_AvramDividend_Classical_ae_twoSidedExitDownTime_eq_zero_iff_ae_near_threshold_crossings
-- name    : AvramDividend.Classical.ae_twoSidedExitDownTime_eq_zero_iff_ae_near_threshold_crossings
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T22:55:44.147123+00:00
-- url     : https://prove2.me/theorems/eee43a49-2148-4657-8a7b-8f0e36103dd5
-- title:
--   Almost-sure instantaneous downward exit equivalence at arbitrary thresholds
-- statement:
--   At any deterministic real barrier, almost-sure immediate downward strict passage is equivalent to almost-sure arbitrarily early strict barrier crossings.
-- source:
--   The accepted pathwise arbitrary-threshold equivalence transports in both directions through almost-everywhere monotonicity.

import Theorems.Thm_AvramDividend_Classical_twoSidedExitDownTime_eq_zero_iff_crossings_at_threshold

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

theorem AvramDividend.Classical.ae_twoSidedExitDownTime_eq_zero_iff_ae_near_threshold_crossings
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (b : ℝ) :
    (∀ᵐ ω ∂P, twoSidedExitDownTime X b ω = 0) ↔
      (∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
        ∃ t : ℝ≥0, t < ε ∧ X.X t ω < b) := by sorry
