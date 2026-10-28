-- Prove2me | Theorems.Thm_FinancialDerivatives_FD05_upperKnockOut_eq_path_sum
-- name    : FinancialDerivatives.FD05.upperKnockOut_eq_path_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T19:38:28.706031+00:00
-- url     : https://prove2.me/theorems/52f3cf40-2ff7-4b24-ac7b-9aa949ea6e9c
-- title:
--   Full-tree upper knock-out value equals finite-path expectation
-- statement:
--   The complete risk-neutral binomial path sum with a survival indicator equals FD-03 backward valuation of the barrier-dependent payoff tree.
-- source:
--   Wilmott, Howison and Dewynne (1995), The Mathematics of Financial Derivatives, Chapter 12, pp. 206–212. Rigorous finite-binomial first-hit analogue.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd05_upperKnockOutTree
import Definitions.Def_fd05_discountedSurvivalPathPrice
import Definitions.Def_fd03_europeanValue

namespace FinancialDerivatives.FD05
open FinancialDerivatives.FD03

theorem upperKnockOut_eq_path_sum (m : BinomialMarket) (N : ℕ)
    (B : ℝ) (monitor : ℕ → Bool) (g : ℝ → ℝ) :
    europeanValue m N
      (upperKnockOutTree m B monitor g N 0 m.initialSpot false) =
    discountedSurvivalPathPrice m N B monitor g := by sorry

end FinancialDerivatives.FD05
