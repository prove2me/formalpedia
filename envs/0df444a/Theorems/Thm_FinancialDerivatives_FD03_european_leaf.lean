-- Prove2me | Theorems.Thm_FinancialDerivatives_FD03_european_leaf
-- name    : FinancialDerivatives.FD03.european_leaf
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T07:56:53.688023+00:00
-- url     : https://prove2.me/theorems/89768ca4-8fd9-4e61-8a76-b75b70e874f7
-- title:
--   European valuation equals its maturity payoff
-- statement:
--   For a horizon of zero periods, the backward-induction price of a terminal payoff c is exactly c.
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapter 10 §10.4, printed p. 188, equation (10.16). Base case of backward induction.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_europeanValue

namespace FinancialDerivatives.FD03

theorem european_leaf (m : BinomialMarket) (c : ℝ) :
    europeanValue m 0 (.leaf c) = c := by sorry

end FinancialDerivatives.FD03
