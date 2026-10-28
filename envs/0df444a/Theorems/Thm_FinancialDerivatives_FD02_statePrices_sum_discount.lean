-- Prove2me | Theorems.Thm_FinancialDerivatives_FD02_statePrices_sum_discount
-- name    : FinancialDerivatives.FD02.statePrices_sum_discount
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T00:08:06.344479+00:00
-- url     : https://prove2.me/theorems/dc57b4aa-6d87-4f95-82ff-b86c1acf275a
-- title:
--   Two state prices add to the unit cash discount factor
-- statement:
--   The total Arrow–Debreu price of the constant one-unit terminal payoff is the bank discount factor 1/R.
--
--   This is an original derived theorem target; a remote compiler must validate its declaration and proof.
-- source:
--   Derived from Wilmott, Howison and Dewynne (1995), §10.1, equation (10.2), p. 182. https://doi.org/10.1017/CBO9780511812545.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd02_TwoStateMarket
import Definitions.Def_fd02_riskNeutralUp

namespace FinancialDerivatives.FD02

/-- Two state prices add to the unit cash discount factor. -/
theorem statePrices_sum_discount (m : TwoStateMarket) :
  riskNeutralUp m / m.growth + (1 - riskNeutralUp m) / m.growth = 1 / m.growth := by sorry

end FinancialDerivatives.FD02
