-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_negative_ruin_overshoot_postpayment_terminal_zero
-- name    : AvramDividend.Classical.avram_wave8_20_original_negative_ruin_overshoot_postpayment_terminal_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T19:19:46.808594+00:00
-- url     : https://prove2.me/theorems/56cbe31f-643a-4692-9630-45d253e81f61
-- title:
--   Actual strictly negative controlled reserve forces zero discounted postpayment continuation at ruin overshoot
-- statement:
--   At any physical time where the actual original controlled reserve is strictly negative, the dividend right limit is no smaller than the dividend paid so far, so the post-rightpayment reserve is still negative. The zero extension of the verification candidate implies the discounted nonnegative continuation payoff is identically zero. In particular this handles the strict negative ruin-overshoot boundary without asserting any payment admissibility at the ruin time.
-- source:
--   Original capped BV Avram Proposition 4(i) ruin-overshoot boundary. This source-faithful result is independent of stochastic compensation and uses only original dividend monotonicity, the literal riskProcess, rightLimit D and zero extension of w on negative reserve. It treats strict negative overshoot only; creeping/zero landing remains separate.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave8_20_original_negative_ruin_overshoot_postpayment_terminal_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ)
    (w : ℝ → ℝ) (hw_neg : ∀ y < 0, w y = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (t : ℝ≥0)
    (hOvershoot : riskProcess X x D t ω < 0) :
    max 0 (Real.exp (-(q * (t : ℝ))) *
      w (x + X.X t ω - rightLimit D t ω)) = 0 := by sorry
