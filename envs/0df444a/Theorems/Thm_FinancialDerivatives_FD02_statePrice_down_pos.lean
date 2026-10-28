-- Prove2me | Theorems.Thm_FinancialDerivatives_FD02_statePrice_down_pos
-- name    : FinancialDerivatives.FD02.statePrice_down_pos
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T00:07:50.579811+00:00
-- url     : https://prove2.me/theorems/98708889-d754-451d-90e5-a10092dade3f
-- title:
--   Down-state Arrow security has positive date-zero price
-- statement:
--   The Arrow–Debreu down-state price (1-q)/R is strictly positive under no-arbitrage and positive bank growth.
--
--   This is an original derived theorem target; a remote compiler must validate its declaration and proof.
-- source:
--   Derived from Wilmott, Howison and Dewynne (1995), §10.1, equation (10.2), p. 182. https://doi.org/10.1017/CBO9780511812545.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd02_TwoStateMarket
import Definitions.Def_fd02_riskNeutralUp
import Definitions.Def_fd02_NoArbitrage

namespace FinancialDerivatives.FD02

/-- Down-state Arrow security has positive date-zero price. -/
theorem statePrice_down_pos (m : TwoStateMarket) (hNA : NoArbitrage m) :
  0 < (1 - riskNeutralUp m) / m.growth := by sorry

end FinancialDerivatives.FD02
