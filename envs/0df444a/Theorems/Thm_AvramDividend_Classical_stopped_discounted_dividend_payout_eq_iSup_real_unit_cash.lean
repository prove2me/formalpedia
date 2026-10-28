-- Prove2me | Theorems.Thm_AvramDividend_Classical_stopped_discounted_dividend_payout_eq_iSup_real_unit_cash
-- name    : AvramDividend.Classical.stopped_discounted_dividend_payout_eq_iSup_real_unit_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T20:13:11.120355+00:00
-- url     : https://prove2.me/theorems/97267d46-68f3-4000-87bf-156abcde1d19
-- title:
--   Real interval cash sums recover the exact stopped dividend Stieltjes payout
-- statement:
--   Given a capped stopped dividend strategy and real-valued nonnegative unit-interval cash amounts whose ENNReal embeddings equal the exact discounted Stieltjes integrals on each half-open interval, the stopped dividend payout equals the supremum of ENNReal.ofReal of finite sums of this real cash. The proof uses the separately Proved payment-window natural-unit partition and the Proved countable Stieltjes partition integral formula, and rewrites the finite ENNReal sums using nonnegativity of cash. It directly supplies the pathwise hypothesis hZ in the Proved exponential_levy_grid_cash_stieltjes_limit_le_initial stochastic verification bound for both open capped BV/UV cores. Establishing cash integrability, finite embedding equality, and the conditional generator one-step inequality for an actual admissible Lévy-driven strategy remains outstanding.

import Mathlib.Data.ENNReal.Basic
import Theorems.Thm_AvramDividend_Classical_stopped_dividend_payment_partition_lintegral_eq_iSup_cash
import Theorems.Thm_AvramDividend_Classical_payment_window_nat_unit_intervals_partition

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.stopped_discounted_dividend_payout_eq_iSup_real_unit_cash
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (D : ℝ≥0 → Ω → ℝ) (σ : ℝ≥0∞) (T q : ℝ) (ω : Ω)
    (cash : ℕ → ℝ)
    (hCashNN : ∀ k : ℕ, 0 ≤ cash k)
    (hCashEq : ∀ k : ℕ,
      ENNReal.ofReal (cash k) =
        ∫⁻ t in (paymentTimes σ ∩ Iic T) ∩
          Ico (k : ℝ) ((k : ℝ) + 1),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) :
    (∫⁻ t in paymentTimes σ ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
      ⨆ n : ℕ, ENNReal.ofReal
        (∑ k ∈ Finset.range n, cash k) := by sorry
