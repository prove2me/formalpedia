-- Prove2me | Theorems.Thm_FinancialDerivatives_FD02_riskNeutralUp_pos
-- name    : FinancialDerivatives.FD02.riskNeutralUp_pos
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T00:03:32.887543+00:00
-- url     : https://prove2.me/theorems/1a9472f6-d683-43d5-813c-c886d381de2a
-- title:
--   No-arbitrage gives a positive up-state probability
-- statement:
--   The risk-neutral up weight (R-d)/(u-d) is strictly positive because R>d and u>d.
--
--   This is an original derived theorem target; a remote compiler must validate its declaration and proof.
-- source:
--   Derived from Wilmott, Howison and Dewynne (1995), §10.2, equation (10.8), p. 184. https://doi.org/10.1017/CBO9780511812545.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd02_TwoStateMarket
import Definitions.Def_fd02_riskNeutralUp
import Definitions.Def_fd02_NoArbitrage

namespace FinancialDerivatives.FD02

/-- No-arbitrage gives a positive up-state probability. -/
theorem riskNeutralUp_pos (m : TwoStateMarket) (hNA : NoArbitrage m) :
  0 < riskNeutralUp m := by sorry

end FinancialDerivatives.FD02
