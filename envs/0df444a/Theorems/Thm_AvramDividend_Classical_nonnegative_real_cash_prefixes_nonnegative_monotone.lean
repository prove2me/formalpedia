-- Prove2me | Theorems.Thm_AvramDividend_Classical_nonnegative_real_cash_prefixes_nonnegative_monotone
-- name    : AvramDividend.Classical.nonnegative_real_cash_prefixes_nonnegative_monotone
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T20:22:38.283821+00:00
-- url     : https://prove2.me/theorems/7ee144ea-01ec-43c9-9ad3-c644f960358c
-- title:
--   Nonnegative real dividend cash yields positive monotone payment prefixes
-- statement:
--   If the real-valued unit-interval dividend cash amounts are nonnegative, every finite prefix sum is nonnegative, and the ENNReal.ofReal-embedded prefix sequence is monotone. The proof uses Finset.sum_nonneg, Finset.sum_range_succ and monotone_nat_of_le_succ. In each open capped BV/UV stochastic core, instantiate cash k ω by the real stopped Stieltjes unit-interval integral, whose nonnegativity follows from ENNReal.toReal_nonneg and whose exact pathwise interpretation is the now-Proved stopped_discounted_dividend_payout_eq_iSup_unit_cash_toReal_of_strategy. This discharges the hPrefixNN and hMono prerequisites in the already Proved exponential_levy_grid_cash_stieltjes_limit_le_initial, leaving integrability, almost-sure measurability, and the conditional HJB step inequality.

import Mathlib.Data.ENNReal.Real
import Mathlib.Order.Monotone.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Range

open scoped ENNReal

theorem AvramDividend.Classical.nonnegative_real_cash_prefixes_nonnegative_monotone
    (cash : ℕ → ℝ) (hCashNN : ∀ k, 0 ≤ cash k) :
    (∀ n : ℕ, 0 ≤ ∑ k ∈ Finset.range n, cash k) ∧
    Monotone (fun n : ℕ =>
      ENNReal.ofReal (∑ k ∈ Finset.range n, cash k)) := by sorry
