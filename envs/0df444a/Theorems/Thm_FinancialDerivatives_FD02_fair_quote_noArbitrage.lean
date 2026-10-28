-- Prove2me | Theorems.Thm_FinancialDerivatives_FD02_fair_quote_noArbitrage
-- name    : FinancialDerivatives.FD02.fair_quote_noArbitrage
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T00:13:53.898261+00:00
-- url     : https://prove2.me/theorems/79c7ae28-f365-4977-9b09-08bb9d5d8676
-- title:
--   The replicating quotation preserves strong no-arbitrage
-- statement:
--   For any signed quantity of a claim at its hedge cost, replace that position by an equivalent stock-and-bank trade. The resulting zero-cost base-market strategy cannot yield positive free payoffs.
--
--   A proof must use the exact published definitions and be accepted by the authoritative Prove2Me compiler.
-- source:
--   Original derived theorem based on Wilmott, Howison and Dewynne (1995), §§3.2,10.3, pp. 33–34 and 187; https://doi.org/10.1017/CBO9780511812545.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd02_TwoStateMarket
import Definitions.Def_fd02_Trade
import Definitions.Def_fd02_terminalPayoff
import Definitions.Def_fd02_Replicates
import Definitions.Def_fd02_replicatingTrade
import Definitions.Def_fd02_initialCost
import Definitions.Def_fd02_riskNeutralUp
import Definitions.Def_fd02_riskNeutralValue
import Definitions.Def_fd02_NoArbitrage
import Definitions.Def_fd02_ClaimNoArbitrage

namespace FinancialDerivatives.FD02

/-- The replicating quotation preserves strong no-arbitrage. -/
theorem fair_quote_noArbitrage (m : TwoStateMarket) (hNA : NoArbitrage m) (H : Bool → ℝ) :
  ClaimNoArbitrage m H (riskNeutralValue m H) := by sorry

end FinancialDerivatives.FD02
