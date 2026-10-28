-- Prove2me | Theorems.Thm_FinancialDerivatives_FD02_zeroCost_terminal_spread
-- name    : FinancialDerivatives.FD02.zeroCost_terminal_spread
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:56:15.826667+00:00
-- url     : https://prove2.me/theorems/4cd65f51-9492-4ac2-b8d5-d3560a706324
-- title:
--   Zero-cost portfolios expose the stock excess returns
-- statement:
--   If initial cost is zero, cash holdings offset the shares at today's price. Both terminal payments are then shares times the stock excess growth over the bank return.
--
--   This is an original derived theorem target; a remote compiler must validate its declaration and proof.
-- source:
--   Derived from Wilmott, Howison and Dewynne (1995), §§2.4,3.2, pp. 30–34. https://doi.org/10.1017/CBO9780511812545.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd02_TwoStateMarket
import Definitions.Def_fd02_Trade
import Definitions.Def_fd02_initialCost
import Definitions.Def_fd02_terminalPayoff

namespace FinancialDerivatives.FD02

/-- Zero-cost portfolios expose the stock excess returns. -/
theorem zeroCost_terminal_spread (m : TwoStateMarket) (t : Trade) (h : initialCost m t = 0) :
  t.cash = -t.shares * m.spot ∧ terminalPayoff m t true = t.shares * m.spot * (m.up - m.growth) ∧ terminalPayoff m t false = t.shares * m.spot * (m.down - m.growth) := by sorry

end FinancialDerivatives.FD02
