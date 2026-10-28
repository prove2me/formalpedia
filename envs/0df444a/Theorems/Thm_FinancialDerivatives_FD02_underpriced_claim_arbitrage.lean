-- Prove2me | Theorems.Thm_FinancialDerivatives_FD02_underpriced_claim_arbitrage
-- name    : FinancialDerivatives.FD02.underpriced_claim_arbitrage
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T00:14:38.016989+00:00
-- url     : https://prove2.me/theorems/c97c5ec6-0783-4313-b893-cbeaefb2a6e3
-- title:
--   Underpricing an attainable claim creates a static arbitrage
-- statement:
--   If the quote is below the hedge cost, buy the claim, short the hedge and invest the surplus. The resulting zero-cost payoff is strictly positive in both states.
--
--   A proof must use the exact published definitions and be accepted by the authoritative Prove2Me compiler.
-- source:
--   Original derived theorem based on Wilmott, Howison and Dewynne (1995), §3.2, pp. 33–34; https://doi.org/10.1017/CBO9780511812545.

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

/-- Underpricing an attainable claim creates a static arbitrage. -/
theorem underpriced_claim_arbitrage (m : TwoStateMarket) (H : Bool → ℝ) (p : ℝ) (hp : p < riskNeutralValue m H) :
  ¬ ClaimNoArbitrage m H p := by sorry

end FinancialDerivatives.FD02
