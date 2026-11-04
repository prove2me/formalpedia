-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_positive_ruin_overshoot_discounted_terminal_zero
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_positive_ruin_overshoot_discounted_terminal_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T15:32:24.253612+00:00
-- url     : https://prove2.me/theorems/d372b8f3-9940-480d-94c1-3b156aed2036
-- title:
--   Negative overshoot at positive original ruin has zero discounted terminal payoff
-- statement:
--   The canonical original W is the pre-rightpayment riskProcess at strictly positive ruin; if this original reserve is negative then the actual negative extension w(y)=0 makes the discounted terminal exactly zero. The zero-clock and survival branches remain distinct. This is a genuine source conditional helper, independent of martingale calculus.
-- source:
--   Original definitions ruinTime, riskProcess, rightLimit and the exact P4-F hW convention.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- At genuine strictly positive ruin, a negative prepayment reserve gives zero discounted terminal extension. -/
theorem AvramDividend.Classical.avram_p4_e_localise_original_positive_ruin_overshoot_discounted_terminal_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (τ : Ω → ℝ≥0) (W : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (w : ℝ → ℝ) (hwneg : ∀ y : ℝ, y < 0 → w y = 0)
    (ω : Ω) (hτpos : 0 < τ ω)
    (hruin : ruinTime X x D ω ≤ (τ ω : ℝ≥0∞))
    (hOvershoot : riskProcess X x D (τ ω) ω < 0) :
    Real.exp (-(q * (τ ω : ℝ))) * w (W ω) = 0 := by sorry
