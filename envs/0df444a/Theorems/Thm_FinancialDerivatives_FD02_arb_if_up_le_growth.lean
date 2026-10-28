-- Prove2me | Theorems.Thm_FinancialDerivatives_FD02_arb_if_up_le_growth
-- name    : FinancialDerivatives.FD02.arb_if_up_le_growth
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:56:54.709671+00:00
-- url     : https://prove2.me/theorems/dcab6c25-fbfb-4c42-89b8-cfc2c4319db1
-- title:
--   Too-high bank growth gives an explicit arbitrage
-- statement:
--   If the up stock factor does not exceed bank growth, shorting shares and depositing the proceeds gives a zero-cost nonnegative terminal payoff, strictly positive in the down state.
--
--   This is an original derived theorem target; a remote compiler must validate its declaration and proof.
-- source:
--   Derived from Wilmott, Howison and Dewynne (1995), §3.2, pp. 33–34. https://doi.org/10.1017/CBO9780511812545.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd02_TwoStateMarket
import Definitions.Def_fd02_Trade
import Definitions.Def_fd02_initialCost
import Definitions.Def_fd02_terminalPayoff
import Definitions.Def_fd02_NoArbitrage

namespace FinancialDerivatives.FD02

/-- Too-high bank growth gives an explicit arbitrage. -/
theorem arb_if_up_le_growth (m : TwoStateMarket) (h : m.up ≤ m.growth) :
  ¬ NoArbitrage m := by sorry

end FinancialDerivatives.FD02
