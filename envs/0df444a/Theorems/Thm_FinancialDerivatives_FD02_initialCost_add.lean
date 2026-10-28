-- Prove2me | Theorems.Thm_FinancialDerivatives_FD02_initialCost_add
-- name    : FinancialDerivatives.FD02.initialCost_add
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:51:19.045226+00:00
-- url     : https://prove2.me/theorems/d19b95c4-2bdf-4844-b9de-2c6d8b86b7a0
-- title:
--   Initial capital is additive across trades
-- statement:
--   For any two stock-and-cash holdings, the cost of holding their sum equals the sum of their separate costs.
--
--   This is an original derived theorem target; a remote compiler must validate its declaration and proof.
-- source:
--   Derived from Wilmott, Howison and Dewynne (1995), §3.2, pp. 33–34. https://doi.org/10.1017/CBO9780511812545.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd02_TwoStateMarket
import Definitions.Def_fd02_Trade
import Definitions.Def_fd02_initialCost

namespace FinancialDerivatives.FD02

/-- Initial capital is additive across trades. -/
theorem initialCost_add (m : TwoStateMarket) (a b : Trade) :
  initialCost m ({ shares := a.shares + b.shares, cash := a.cash + b.cash } : Trade) = initialCost m a + initialCost m b := by sorry

end FinancialDerivatives.FD02
