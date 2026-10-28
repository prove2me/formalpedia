-- Prove2me | Theorems.Thm_AvramDividend_Classical_stopped_discounted_unit_cash_ne_top_of_strategy
-- name    : AvramDividend.Classical.stopped_discounted_unit_cash_ne_top_of_strategy
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T19:58:09.74699+00:00
-- url     : https://prove2.me/theorems/ee7844fe-35f8-4385-9f1e-50b416d7b3d6
-- title:
--   Every stopped discounted unit-interval Stieltjes cash amount is finite
-- statement:
--   For any admissible nondecreasing dividend strategy, nonnegative discount rate and finite horizon, the exact stopped discounted Stieltjes integral over the intersection of the payment window with a half-open unit time interval is finite. It is bounded by the corresponding undiscounted measure, then by the total stopped payment-window mass, whose finiteness is already canonically Proved. This gives the pointwise finiteness required to define real-valued cash as ENNReal.toReal of exact interval integrals in stopped_discounted_dividend_payout_eq_iSup_real_unit_cash, feeding the Proved exponential_levy_grid_cash_stieltjes_limit_le_initial and both BV/UV stochastic cores. Expected integrability and stopped generator inequality remain open.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_paymentWindow_finite_of_strategy
import Theorems.Thm_AvramDividend_Classical_discounted_stieltjes_lintegral_le_measure
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.stopped_discounted_unit_cash_ne_top_of_strategy
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) (σ : ℝ≥0∞) (T : ℝ≥0)
    (ω : Ω) (k : ℕ) :
    (∫⁻ t in (paymentTimes σ ∩ Iic (T : ℝ)) ∩
      Ico (k : ℝ) ((k : ℝ) + 1),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≠ ⊤ := by sorry
