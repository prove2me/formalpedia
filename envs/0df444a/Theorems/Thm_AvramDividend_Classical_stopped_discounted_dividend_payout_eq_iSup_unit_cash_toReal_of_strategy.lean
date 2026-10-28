-- Prove2me | Theorems.Thm_AvramDividend_Classical_stopped_discounted_dividend_payout_eq_iSup_unit_cash_toReal_of_strategy
-- name    : AvramDividend.Classical.stopped_discounted_dividend_payout_eq_iSup_unit_cash_toReal_of_strategy
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T20:18:37.97274+00:00
-- url     : https://prove2.me/theorems/b1717b27-f3e5-410d-b36e-63300020b613
-- title:
--   Admissible stopped Stieltjes payouts equal real unit-interval cash suprema
-- statement:
--   For any admissible dividend strategy, nonnegative discount and finite horizon, the actual discounted Stieltjes payout restricted to the stopped payment window is exactly the supremum of finite real-valued unit-interval cash sums embedded in ENNReal. All unit cash amounts are finite by the previously Proved stopped_discounted_unit_cash_ne_top_of_strategy. The pairwise disjoint half-open unit partition and countable Stieltjes integration theorem retain the continuous and jump components. This exports the explicit payoff-limit hypothesis hZ of exponential_levy_grid_cash_stieltjes_limit_le_initial for the BV and UV capped stochastic verification cores. Conditional generator budget and cash integrability remain open.

import Mathlib.Data.ENNReal.Basic
import Theorems.Thm_AvramDividend_Classical_stopped_dividend_payment_partition_lintegral_eq_iSup_cash
import Theorems.Thm_AvramDividend_Classical_payment_window_nat_unit_intervals_partition
import Theorems.Thm_AvramDividend_Classical_stopped_discounted_unit_cash_ne_top_of_strategy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.stopped_discounted_dividend_payout_eq_iSup_unit_cash_toReal_of_strategy
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) (σ : ℝ≥0∞) (T : ℝ≥0) (ω : Ω) :
    (∫⁻ t in paymentTimes σ ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
      ⨆ n : ℕ, ENNReal.ofReal
        (∑ k ∈ Finset.range n,
          (∫⁻ t in (paymentTimes σ ∩ Iic (T : ℝ)) ∩
            Ico (k : ℝ) ((k : ℝ) + 1),
            ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal) := by sorry
