-- Prove2me | Theorems.Thm_AvramDividend_Classical_stopped_unit_cash_integrable_of_stopped_payout_integrable
-- name    : AvramDividend.Classical.stopped_unit_cash_integrable_of_stopped_payout_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T22:06:53.791828+00:00
-- url     : https://prove2.me/theorems/c4c4446c-e1a6-4f86-8959-29278e7d6626
-- title:
--   Stopped exact Stieltjes unit cash integrable from integrable stopped total payout
-- statement:
--   If the actual whole discounted Stieltjes payout stopped at ruin and a finite horizon has an integrable real value, every discounted stopped half-open unit interval cash payout is integrable. The proof uses measurability of each unit cash block, finite total Stieltjes measure on the stopped payment window, discount domination for q≥0, monotonicity of nonnegative integrals and toReal_mono. This avoids assuming integrability of cumulative D(T+1) including irrelevant post-ruin dividends. It discharges each hCashI hypothesis in the root-connected stopped_dividend_grid_verification_of_integrable_cash_budget, for either bounded-variation or unbounded-variation capped stochastic verification.

import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Data.ENNReal.Real
import Theorems.Thm_AvramDividend_Classical_discounted_stieltjes_lintegral_le_measure
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_paymentWindow_finite_of_strategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_stopped_discounted_unit_cash_measurable_of_strategy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.stopped_unit_cash_integrable_of_stopped_payout_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (T : ℝ≥0)
    (hTotalI : Integrable (fun ω : Ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal) P)
    (k : ℕ) :
    Integrable (fun ω : Ω =>
      (∫⁻ t in
        (paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ)) ∩
          Ico (k : ℝ) ((k : ℝ) + 1),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal) P := by sorry
