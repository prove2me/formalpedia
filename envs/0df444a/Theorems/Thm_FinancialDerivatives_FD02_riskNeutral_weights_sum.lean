-- Prove2me | Theorems.Thm_FinancialDerivatives_FD02_riskNeutral_weights_sum
-- name    : FinancialDerivatives.FD02.riskNeutral_weights_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T00:06:13.321204+00:00
-- url     : https://prove2.me/theorems/3b91aac4-f2e4-4f76-8e0a-9a16c9d23db5
-- title:
--   Risk-neutral probabilities are positive and normalised
-- statement:
--   The unique up/down risk-neutral weights sum to one and each is strictly positive under strong no-arbitrage.
--
--   This is an original derived theorem target; a remote compiler must validate its declaration and proof.
-- source:
--   Derived from Wilmott, Howison and Dewynne (1995), §10.2, equations (10.4) and (10.8), pp. 183–184. https://doi.org/10.1017/CBO9780511812545.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd02_TwoStateMarket
import Definitions.Def_fd02_riskNeutralUp
import Definitions.Def_fd02_NoArbitrage

namespace FinancialDerivatives.FD02

/-- Risk-neutral probabilities are positive and normalised. -/
theorem riskNeutral_weights_sum (m : TwoStateMarket) (hNA : NoArbitrage m) :
  riskNeutralUp m + (1 - riskNeutralUp m) = 1 ∧ 0 < riskNeutralUp m ∧ 0 < 1 - riskNeutralUp m := by sorry

end FinancialDerivatives.FD02
