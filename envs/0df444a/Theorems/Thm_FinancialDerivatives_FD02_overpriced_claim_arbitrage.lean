-- Prove2me | Theorems.Thm_FinancialDerivatives_FD02_overpriced_claim_arbitrage
-- name    : FinancialDerivatives.FD02.overpriced_claim_arbitrage
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T00:14:21.415192+00:00
-- url     : https://prove2.me/theorems/cb23f0fe-ef78-4352-86dd-7bc208000abe
-- title:
--   Overpricing an attainable claim creates a static arbitrage
-- statement:
--   If the quoted claim price exceeds the hedge cost, short the claim, buy the hedge and invest the difference. The resulting trade costs zero and earns a positive bank payoff in both states.
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

/-- Overpricing an attainable claim creates a static arbitrage. -/
theorem overpriced_claim_arbitrage (m : TwoStateMarket) (H : Bool → ℝ) (p : ℝ) (hp : riskNeutralValue m H < p) :
  ¬ ClaimNoArbitrage m H p := by sorry

end FinancialDerivatives.FD02
