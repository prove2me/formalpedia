-- Prove2me | Theorems.Thm_FinancialDerivatives_FD02_FD01_price_eq_riskNeutralValue
-- name    : FinancialDerivatives.FD02.FD01_price_eq_riskNeutralValue
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T00:11:36.122621+00:00
-- url     : https://prove2.me/theorems/76a36ff7-9dfe-4861-b12f-a142bd6dfefd
-- title:
--   Constructed FD-01 valuation agrees with the two-state expectation
-- statement:
--   The actual FD-01 finite-price system built from positive two-state weights values every signed payoff at its one-period discounted risk-neutral expectation.
--
--   This is an original derived proof obligation in the private FD-02 authoring graph.
-- source:
--   Wilmott, Howison and Dewynne (1995), §10.1, equation (10.2), p. 182; original finite-market formalisation. https://doi.org/10.1017/CBO9780511812545.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Definitions.Def_fd01_FinitePriceSystem
import Definitions.Def_fd01_price
import Definitions.Def_fd02_TwoStateMarket
import Definitions.Def_fd02_riskNeutralUp
import Definitions.Def_fd02_riskNeutralValue
import Definitions.Def_fd02_toFD01PriceSystem

namespace FinancialDerivatives.FD02

/-- Constructed FD-01 valuation agrees with the two-state expectation. -/
theorem FD01_price_eq_riskNeutralValue (m : TwoStateMarket) (hq0 : 0 < riskNeutralUp m) (hq1 : riskNeutralUp m < 1) (H : Bool → ℝ) :
  (toFD01PriceSystem m hq0 hq1).price H = riskNeutralValue m H := by sorry

end FinancialDerivatives.FD02
