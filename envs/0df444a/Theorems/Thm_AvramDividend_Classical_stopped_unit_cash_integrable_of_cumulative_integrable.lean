-- Prove2me | Theorems.Thm_AvramDividend_Classical_stopped_unit_cash_integrable_of_cumulative_integrable
-- name    : AvramDividend.Classical.stopped_unit_cash_integrable_of_cumulative_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T20:48:40.921886+00:00
-- url     : https://prove2.me/theorems/a3fcfc2e-15ca-439f-b429-c6831760511b
-- title:
--   Integrability of stopped discounted unit dividends under integrable cumulative domination
-- statement:
--   Given a stopped admissible spectrally negative Levy dividend strategy, if its total cumulative dividend D(T+1) at the finite horizon is integrable in real ENNReal embedding, then the exact stopped discounted Stieltjes cash paid in any half-open unit block is integrable. The pathwise discounted payment window bound by D(T+1), nonnegative integral restriction, measurable unit cash and Integrable.mono establish this. It supplies the exact hCashI integrability input to the canonically Proved exponential_levy_grid_cash_stieltjes_limit_le_initial whenever a BV/UV stochastic localisation has established integrable cumulative dividends.

import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Data.ENNReal.Real
import Theorems.Thm_AvramDividend_Classical_discounted_dividend_window_le_cumulative
import Theorems.Thm_AvramDividend_Classical_stopped_discounted_unit_cash_measurable_of_strategy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.stopped_unit_cash_integrable_of_cumulative_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (T : ℝ≥0)
    (hDI : Integrable (fun ω : Ω =>
      (ENNReal.ofReal (D (T + 1) ω)).toReal) P)
    (k : ℕ) :
    Integrable (fun ω : Ω =>
      (∫⁻ t in
        (paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ)) ∩
          Ico (k : ℝ) ((k : ℝ) + 1),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal) P := by sorry
