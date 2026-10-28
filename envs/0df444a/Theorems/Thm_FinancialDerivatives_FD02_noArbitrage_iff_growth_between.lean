-- Prove2me | Theorems.Thm_FinancialDerivatives_FD02_noArbitrage_iff_growth_between
-- name    : FinancialDerivatives.FD02.noArbitrage_iff_growth_between
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:59:55.05956+00:00
-- url     : https://prove2.me/theorems/d587e1a9-2934-4ff0-8bb4-16dd573f1f00
-- title:
--   Two-state no-arbitrage exactly means strict return separation
-- statement:
--   Strong no-arbitrage holds exactly when d<R<u, with d<u and positive stock/bank prices already included in the market structure.
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

/-- Two-state no-arbitrage exactly means strict return separation. -/
theorem noArbitrage_iff_growth_between (m : TwoStateMarket) :
  NoArbitrage m ↔ m.down < m.growth ∧ m.growth < m.up := by sorry

end FinancialDerivatives.FD02
