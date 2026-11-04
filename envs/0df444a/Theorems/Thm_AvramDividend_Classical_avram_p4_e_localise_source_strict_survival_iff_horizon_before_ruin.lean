-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_source_strict_survival_iff_horizon_before_ruin
-- name    : AvramDividend.Classical.avram_p4_e_localise_source_strict_survival_iff_horizon_before_ruin
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T16:43:55.647163+00:00
-- url     : https://prove2.me/theorems/107f238b-9fa3-403d-8d6b-a4a2604e71f6
-- title:
--   Original exact ruin-truncated stopped-clock strict survival iff fixed horizon precedes ruin
-- statement:
--   For the exact original stopped ruin clock, strict pre-ruin survival at the clock is equivalent to the fixed integer horizon preceding the genuine ruin time, even when ruin is infinite or occurs exactly at the horizon. This identifies precisely the branch of the original post-rightpayment terminal payoff and enables faithful survival indicator decomposition.
-- source:
--   Exact source τ equation from P4-F 0dda1be7-9d8b-41e0-ae51-55fab5c38e22; finite deterministic n and ENNReal minimum.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The exact ruin-truncated clock is strictly before ruin exactly when the deterministic horizon is strictly before ruin. This includes infinite ruin. -/
theorem AvramDividend.Classical.avram_p4_e_localise_source_strict_survival_iff_horizon_before_ruin
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal) :
    ∀ ω, ((τ ω : ℝ≥0∞) < ruinTime X x D ω) ↔
      ((n : ℝ≥0∞) < ruinTime X x D ω) := by sorry
