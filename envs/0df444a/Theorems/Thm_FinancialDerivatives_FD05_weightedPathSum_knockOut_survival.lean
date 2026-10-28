-- Prove2me | Theorems.Thm_FinancialDerivatives_FD05_weightedPathSum_knockOut_survival
-- name    : FinancialDerivatives.FD05.weightedPathSum_knockOut_survival
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T19:44:26.536972+00:00
-- url     : https://prove2.me/theorems/e405b34c-d8c5-408b-9bc7-f53783f1fda0
-- title:
--   Connect recursive tree weights with explicit surviving-history weights
-- statement:
--   FD-03's recursively weighted payoff-tree valuation of a knock-out contract agrees after discounting with the FD-05 explicit full-history first-hit sum.
-- source:
--   Wilmott, Howison and Dewynne (1995), The Mathematics of Financial Derivatives, Chapter 12, pp. 206–212. Rigorous finite-binomial first-hit analogue.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_weightedPathSum
import Definitions.Def_fd05_upperKnockOutTree
import Definitions.Def_fd05_discountedSurvivalPathPrice

namespace FinancialDerivatives.FD05
open FinancialDerivatives.FD03

theorem weightedPathSum_knockOut_survival (m : BinomialMarket)
    (N : ℕ) (B : ℝ) (monitor : ℕ → Bool) (g : ℝ → ℝ) :
    weightedPathSum m N (upperKnockOutTree m B monitor g N 0 m.initialSpot false) / m.growth ^ N =
      discountedSurvivalPathPrice m N B monitor g := by sorry

end FinancialDerivatives.FD05
