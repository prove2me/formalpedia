-- Prove2me | Theorems.Thm_AvramDividend_Classical_stopped_discounted_dividend_payout_measurable_of_strategy
-- name    : AvramDividend.Classical.stopped_discounted_dividend_payout_measurable_of_strategy
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T20:54:46.153678+00:00
-- url     : https://prove2.me/theorems/f3646bf4-5d30-4c44-9252-ddfa5ee789b8
-- title:
--   Measurability of exact stopped Stieltjes dividend payout at any finite capped horizon
-- statement:
--   The complete stopped discounted Stieltjes payout, including continuous dividends and right-jump atoms, is measurable as a function of the Levy sample path at an arbitrary nonnegative real horizon T. The canonically Proved stopped_dividend_payout_eq_iSup_unit_cash_toReal_of_strategy expresses it exactly as the countable supremum of finite real cash prefixes, and the canonically Proved stopped_real_cash_prefix_measurable_of_strategy gives measurability of every term. Apply Mathlib Measurable.iSup. This is reusable in both BV and UV finite-horizon stochastic verification and their expectation/localisation passages; unlike the existing truncated_dividend_payoff_measurable, it covers arbitrary ℝ≥0 horizons, not only n:ℕ.

import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Theorems.Thm_AvramDividend_Classical_stopped_discounted_dividend_payout_eq_iSup_unit_cash_toReal_of_strategy
import Theorems.Thm_AvramDividend_Classical_stopped_discounted_real_cash_prefix_measurable_of_strategy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.stopped_discounted_dividend_payout_measurable_of_strategy
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (T : ℝ≥0) :
    Measurable (fun ω : Ω =>
      ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by sorry
