-- Prove2me | Theorems.Thm_FinancialDerivatives_FD02_noArbitrage_implies_growth_lt_up
-- name    : FinancialDerivatives.FD02.noArbitrage_implies_growth_lt_up
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:57:59.552794+00:00
-- url     : https://prove2.me/theorems/bfb9230a-3b8f-4b57-b4fc-ae1e2135f8d4
-- title:
--   No-arbitrage requires bank growth below the up factor
-- statement:
--   A no-arbitrage market must satisfy the strict inequality R<u. Equality is excluded by the down-state gain from shorting shares.
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

/-- No-arbitrage requires bank growth below the up factor. -/
theorem noArbitrage_implies_growth_lt_up (m : TwoStateMarket) (hNA : NoArbitrage m) :
  m.growth < m.up := by sorry

end FinancialDerivatives.FD02
