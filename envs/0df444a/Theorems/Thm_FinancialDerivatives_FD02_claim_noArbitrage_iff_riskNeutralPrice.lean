-- Prove2me | Theorems.Thm_FinancialDerivatives_FD02_claim_noArbitrage_iff_riskNeutralPrice
-- name    : FinancialDerivatives.FD02.claim_noArbitrage_iff_riskNeutralPrice
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T00:14:54.680834+00:00
-- url     : https://prove2.me/theorems/50307e16-2a5e-4718-9c5d-d1a56863574e
-- title:
--   An attainable claim has exactly one arbitrage-free quoted price
-- statement:
--   In a strictly arbitrage-free complete two-state market, allowing trade in a claim preserves the no-arbitrage condition exactly at its replicating price, which equals discounted risk-neutral expectation.
--
--   A proof must use the exact published definitions and be accepted by the authoritative Prove2Me compiler.
-- source:
--   Original derived theorem based on Wilmott, Howison and Dewynne (1995), §§3.2,10.1–10.3, pp. 33–34 and 180–187; https://doi.org/10.1017/CBO9780511812545.

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

/-- An attainable claim has exactly one arbitrage-free quoted price. -/
theorem claim_noArbitrage_iff_riskNeutralPrice (m : TwoStateMarket) (hNA : NoArbitrage m) (H : Bool → ℝ) (p : ℝ) :
  ClaimNoArbitrage m H p ↔ p = riskNeutralValue m H := by sorry

end FinancialDerivatives.FD02
