-- Prove2me | Theorems.Thm_FinancialDerivatives_FD02_noArbitrage_of_growth_between
-- name    : FinancialDerivatives.FD02.noArbitrage_of_growth_between
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:58:11.600156+00:00
-- url     : https://prove2.me/theorems/68bd4c57-d62e-45a0-95f1-4c0553aaddcf
-- title:
--   Strict return separation precludes zero-cost arbitrage
-- statement:
--   If the bank growth lies strictly between the down and up factors, any nonzero zero-cost stock position creates opposite-signed state payoffs. Hence no arbitrage exists.
--
--   This is an original derived theorem target; a remote compiler must validate its declaration and proof.
-- source:
--   Derived from Wilmott, Howison and Dewynne (1995), §§2.4,3.2, pp. 30–34. https://doi.org/10.1017/CBO9780511812545.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd02_TwoStateMarket
import Definitions.Def_fd02_Trade
import Definitions.Def_fd02_initialCost
import Definitions.Def_fd02_terminalPayoff
import Definitions.Def_fd02_NoArbitrage

namespace FinancialDerivatives.FD02

/-- Strict return separation precludes zero-cost arbitrage. -/
theorem noArbitrage_of_growth_between (m : TwoStateMarket) (hd : m.down < m.growth) (hu : m.growth < m.up) :
  NoArbitrage m := by sorry

end FinancialDerivatives.FD02
