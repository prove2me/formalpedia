-- Prove2me | Theorems.Thm_FinancialDerivatives_FD02_noArbitrage_implies_down_lt_growth
-- name    : FinancialDerivatives.FD02.noArbitrage_implies_down_lt_growth
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:57:45.613167+00:00
-- url     : https://prove2.me/theorems/f887381c-4539-4f00-b7e7-32f033c2ffa4
-- title:
--   No-arbitrage requires bank growth above the down factor
-- statement:
--   A no-arbitrage market must satisfy the strict inequality d<R. Equality is excluded because the up state offers a zero-cost gain.
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

/-- No-arbitrage requires bank growth above the down factor. -/
theorem noArbitrage_implies_down_lt_growth (m : TwoStateMarket) (hNA : NoArbitrage m) :
  m.down < m.growth := by sorry

end FinancialDerivatives.FD02
