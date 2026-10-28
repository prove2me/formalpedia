-- Prove2me | Theorems.Thm_FinancialDerivatives_FD02_riskNeutralUp_lt_one
-- name    : FinancialDerivatives.FD02.riskNeutralUp_lt_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T00:03:48.397571+00:00
-- url     : https://prove2.me/theorems/46e2f96c-10cf-43cd-ad25-8ae7a52a8ee1
-- title:
--   No-arbitrage gives up-state probability below one
-- statement:
--   The risk-neutral up weight is strictly less than one because R<u and u>d.
--
--   This is an original derived theorem target; a remote compiler must validate its declaration and proof.
-- source:
--   Derived from Wilmott, Howison and Dewynne (1995), §10.2, equation (10.8), p. 184. https://doi.org/10.1017/CBO9780511812545.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd02_TwoStateMarket
import Definitions.Def_fd02_riskNeutralUp
import Definitions.Def_fd02_NoArbitrage

namespace FinancialDerivatives.FD02

/-- No-arbitrage gives up-state probability below one. -/
theorem riskNeutralUp_lt_one (m : TwoStateMarket) (hNA : NoArbitrage m) :
  riskNeutralUp m < 1 := by sorry

end FinancialDerivatives.FD02
