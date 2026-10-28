-- Prove2me | Theorems.Thm_FinancialDerivatives_FD02_replicatingTrade_down
-- name    : FinancialDerivatives.FD02.replicatingTrade_down
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T00:12:07.661997+00:00
-- url     : https://prove2.me/theorems/2aab80b0-734d-4dc1-8ae4-2bac5d11ed3e
-- title:
--   Constructed portfolio pays the down-state claim
-- statement:
--   The same fixed hedge reproduces the down-state payment exactly.
--
--   A proof must use the exact published definitions and be accepted by the authoritative Prove2Me compiler.
-- source:
--   Original derived theorem based on Wilmott, Howison and Dewynne (1995), §2.4, p. 30 and §10.3, p. 187; https://doi.org/10.1017/CBO9780511812545.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd02_TwoStateMarket
import Definitions.Def_fd02_Trade
import Definitions.Def_fd02_terminalPayoff
import Definitions.Def_fd02_Replicates
import Definitions.Def_fd02_replicatingTrade

namespace FinancialDerivatives.FD02

/-- Constructed portfolio pays the down-state claim. -/
theorem replicatingTrade_down (m : TwoStateMarket) (H : Bool → ℝ) :
  terminalPayoff m (replicatingTrade m H) false = H false := by sorry

end FinancialDerivatives.FD02
