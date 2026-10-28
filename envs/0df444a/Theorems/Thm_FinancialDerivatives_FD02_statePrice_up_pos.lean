-- Prove2me | Theorems.Thm_FinancialDerivatives_FD02_statePrice_up_pos
-- name    : FinancialDerivatives.FD02.statePrice_up_pos
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T00:07:36.002893+00:00
-- url     : https://prove2.me/theorems/07cb0a62-8e4d-4347-8cea-69f5328e7f96
-- title:
--   Up-state Arrow security has positive date-zero price
-- statement:
--   The Arrow–Debreu up-state price q/R is strictly positive under no-arbitrage and positive bank growth.
--
--   This is an original derived theorem target; a remote compiler must validate its declaration and proof.
-- source:
--   Derived from Wilmott, Howison and Dewynne (1995), §10.1, equation (10.2), p. 182. https://doi.org/10.1017/CBO9780511812545.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd02_TwoStateMarket
import Definitions.Def_fd02_riskNeutralUp
import Definitions.Def_fd02_NoArbitrage

namespace FinancialDerivatives.FD02

/-- Up-state Arrow security has positive date-zero price. -/
theorem statePrice_up_pos (m : TwoStateMarket) (hNA : NoArbitrage m) :
  0 < riskNeutralUp m / m.growth := by sorry

end FinancialDerivatives.FD02
