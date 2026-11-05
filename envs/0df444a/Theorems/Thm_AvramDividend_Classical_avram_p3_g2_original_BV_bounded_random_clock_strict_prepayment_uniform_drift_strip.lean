-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_BV_bounded_random_clock_strict_prepayment_uniform_drift_strip
-- name    : AvramDividend.Classical.avram_p3_g2_original_BV_bounded_random_clock_strict_prepayment_uniform_drift_strip
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T23:25:13.036452+00:00
-- url     : https://prove2.me/theorems/635fc873-5a48-47ca-b8a0-6ed67cc0c97c
-- title:
--   Actual original BV bounded sample-dependent clock has a uniform strict pre-ruin prepayment reserve strip
-- statement:
--   At any possibly path-dependent physical clock τ bounded by finite H, on the same original BV full-probability event, the genuine pre-rightpayment reserve before ruin lies between zero and x + H·max(drift,0). Handles zero clocks, cap contact and ruin exactly via strict survival and does not require τ to be a stopping time or measurable for the pathwise assertion.
-- source:
--   The new public/proved 5dfadcd5 G2 single-event all-clock drift strip; deterministic time bound and original Levy drift domination, no other P3 obligations.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_BV_simultaneous_all_clock_strict_preruin_prepayment_drift_strip

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_g2_original_BV_bounded_random_clock_strict_prepayment_uniform_drift_strip
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (hXzero : ∀ ω, X.X 0 ω = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (H : ℝ≥0) (τ : Ω → ℝ≥0) (hτBound : ∀ ω, τ ω ≤ H) :
    ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ riskProcess X x D (τ ω) ω ∧
      riskProcess X x D (τ ω) ω ≤
        x + (H : ℝ) * max X.drift 0 := by sorry
