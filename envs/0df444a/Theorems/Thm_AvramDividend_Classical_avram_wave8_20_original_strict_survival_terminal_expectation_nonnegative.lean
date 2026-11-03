-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_strict_survival_terminal_expectation_nonnegative
-- name    : AvramDividend.Classical.avram_wave8_20_original_strict_survival_terminal_expectation_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T00:04:01.717284+00:00
-- url     : https://prove2.me/theorems/bc3122fd-ab95-4e38-a419-53963fad2c09
-- title:
--   Nonnegative expected original strictly surviving postrightpayment terminal without stochastic assumptions
-- statement:
--   For every original source law and physical finite horizon, the expected killed strictly surviving discounted postrightpayment positive-part continuation is nonnegative, including ruin at equality and overshoot.
-- source:
--   Original source risk process, ruinTime, rightLimit and discounted postrightpayment HJB positive-part terminal. The integrand is nonnegative for every original sample path in both exact strict survival and killed branches, hence real integral_nonneg. No assumptions of generator, supermartingale, HJB, BV or terminal integrability are introduced; this merely supplies the sign interface to the original full Stieltjes budget.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave8_20_original_strict_survival_terminal_expectation_nonnegative
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (q : ℝ)
    (H : ℝ≥0) :
    0 ≤ ∫ ω, (if (H : ℝ≥0∞) < ruinTime X x D ω then
      max 0 (Real.exp (-(q * (H : ℝ))) *
        w (x + X.X H ω - rightLimit D H ω))
      else 0) ∂P := by sorry
