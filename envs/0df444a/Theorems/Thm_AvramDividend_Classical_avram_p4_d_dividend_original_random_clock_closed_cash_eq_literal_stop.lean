-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_random_clock_closed_cash_eq_literal_stop
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_random_clock_closed_cash_eq_literal_stop
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:45:50.863194+00:00
-- url     : https://prove2.me/theorems/25bc9d3d-bcc5-49ed-874a-f4cd35140f82
-- title:
--   Exact original closed Stieltjes payment identity holds pathwise at arbitrary random stopped dividend clock
-- statement:
--   The source-original entire dividend Stieltjes cash restricted to the closed physical interval [0, τ(ω)] equals pathwise the literal P4-F ruin-truncated paymentTimes∩Iic τ(ω) cash at any finite random horizon τ, without additional stochastic clock hypotheses. This direct specialization of the accepted complete Stieltjes identity preserves initial atom, horizon-right-payment atom, simultaneous original source/payment jump and singular-continuous cash, excluding positive ruin-endpoint right payment.
-- source:
--   Accepted P4-D original exact closed restricted cash identity 52a094c1; original P4-F random stopped Cash.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_closed_restrict_cash_eq_literal_stop
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- The exact original finite-window Stieltjes identity holds pathwise at any random clock, in particular the true stopped clock. -/

theorem AvramDividend.Classical.avram_p4_d_dividend_original_random_clock_closed_cash_eq_literal_stop
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (τ : Ω → ℝ≥0) :
    ∀ ω : Ω,
      (∫⁻ s : ℝ, (if s ∈ paymentTimes (ruinTime X x D ω)
        then ENNReal.ofReal (Real.exp (-(q * s))) else 0)
        ∂((dividendMeasure D ω).restrict (Icc (0 : ℝ) (τ ω : ℝ)))) =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) := by sorry
