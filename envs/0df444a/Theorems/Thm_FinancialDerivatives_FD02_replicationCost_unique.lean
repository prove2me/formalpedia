-- Prove2me | Theorems.Thm_FinancialDerivatives_FD02_replicationCost_unique
-- name    : FinancialDerivatives.FD02.replicationCost_unique
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T00:13:34.425005+00:00
-- url     : https://prove2.me/theorems/802195bf-ed2f-4cd7-8078-a6adddeecd36
-- title:
--   Every exact hedge has one common no-arbitrage cost
-- statement:
--   If any trade reproduces the claim, its date-zero cost equals the discounted expectation computed from the unique risk-neutral stock weight.
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

namespace FinancialDerivatives.FD02

/-- Every exact hedge has one common no-arbitrage cost. -/
theorem replicationCost_unique (m : TwoStateMarket) (H : Bool → ℝ) (t : Trade) (ht : Replicates m t H) :
  initialCost m t = riskNeutralValue m H := by sorry

end FinancialDerivatives.FD02
