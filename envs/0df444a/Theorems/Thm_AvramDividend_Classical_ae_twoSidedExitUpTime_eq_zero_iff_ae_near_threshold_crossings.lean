-- Prove2me | Theorems.Thm_AvramDividend_Classical_ae_twoSidedExitUpTime_eq_zero_iff_ae_near_threshold_crossings
-- name    : AvramDividend.Classical.ae_twoSidedExitUpTime_eq_zero_iff_ae_near_threshold_crossings
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T22:55:19.068192+00:00
-- url     : https://prove2.me/theorems/0ba38f61-bfa0-4fa0-ac62-68864d4f8f90
-- title:
--   Almost-sure instantaneous upward exit equivalence at arbitrary thresholds
-- statement:
--   At any deterministic real barrier, almost-sure immediate upward strict passage is equivalent to almost-sure arbitrarily early strict barrier crossings.
-- source:
--   The accepted pathwise arbitrary-threshold equivalence transports in both directions through almost-everywhere monotonicity.

import Theorems.Thm_AvramDividend_Classical_twoSidedExitUpTime_eq_zero_iff_crossings_at_threshold

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

theorem AvramDividend.Classical.ae_twoSidedExitUpTime_eq_zero_iff_ae_near_threshold_crossings
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (b : ℝ) :
    (∀ᵐ ω ∂P, twoSidedExitUpTime X b ω = 0) ↔
      (∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
        ∃ t : ℝ≥0, t < ε ∧ b < X.X t ω) := by sorry
