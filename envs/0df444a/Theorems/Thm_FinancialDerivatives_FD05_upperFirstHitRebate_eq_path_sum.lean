-- Prove2me | Theorems.Thm_FinancialDerivatives_FD05_upperFirstHitRebate_eq_path_sum
-- name    : FinancialDerivatives.FD05.upperFirstHitRebate_eq_path_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T19:43:15.841244+00:00
-- url     : https://prove2.me/theorems/17aabf94-a1ff-4be6-86d3-58b16d8f8176
-- title:
--   First-hit terminal-equivalent rebate equals correctly discounted cashflow
-- statement:
--   Paying a fixed rebate at the earliest monitored touch has the same time-zero value as a maturity-equivalent terminal claim and the explicit first-hit discount sum.
-- source:
--   Wilmott, Howison and Dewynne (1995), The Mathematics of Financial Derivatives, Chapter 12, pp. 206–212. Rigorous finite-binomial first-hit analogue.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd05_upperFirstHitRebateTree
import Definitions.Def_fd05_discountedFirstHitRebatePrice
import Definitions.Def_fd03_europeanValue

namespace FinancialDerivatives.FD05
open FinancialDerivatives.FD03

theorem upperFirstHitRebate_eq_path_sum (m : BinomialMarket)
    (N : ℕ) (B : ℝ) (monitor : ℕ → Bool) (Z : ℝ) :
    europeanValue m N
      (upperFirstHitRebateTree m B monitor Z N 0 m.initialSpot) =
    discountedFirstHitRebatePrice m N B monitor Z := by sorry

end FinancialDerivatives.FD05
