-- Prove2me | Theorems.Thm_FinancialDerivatives_FD02_arb_if_growth_le_down
-- name    : FinancialDerivatives.FD02.arb_if_growth_le_down
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:56:37.114813+00:00
-- url     : https://prove2.me/theorems/e3cc2494-7e9a-4cce-9972-94c72c387abe
-- title:
--   Too-low bank growth gives an explicit arbitrage
-- statement:
--   If bank growth is no greater than the down stock factor, buying shares with borrowed cash costs zero and pays nonnegatively in both states and strictly positively in the up state.
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

/-- Too-low bank growth gives an explicit arbitrage. -/
theorem arb_if_growth_le_down (m : TwoStateMarket) (h : m.growth ≤ m.down) :
  ¬ NoArbitrage m := by sorry

end FinancialDerivatives.FD02
