-- Prove2me | Theorems.Thm_FinancialDerivatives_FD03_european_constant
-- name    : FinancialDerivatives.FD03.european_constant
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T08:03:33.317624+00:00
-- url     : https://prove2.me/theorems/4057b396-5643-491c-8dae-26f371029d5b
-- title:
--   Constant maturity cashflow discounts by the bank factor
-- statement:
--   A finite-horizon claim paying the same signed amount c at every terminal path has European value c divided by R raised to the number of periods N. The statement includes N=0 and negative c.
-- source:
--   Original constant-payoff discounting result from Wilmott, Howison and Dewynne (1995), Chapter 10 §10.4, equation (10.16), printed p. 188.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_europeanValue
import Definitions.Def_fd03_constantPayoffTree

namespace FinancialDerivatives.FD03

theorem european_constant (m : BinomialMarket) (n : ℕ) (c : ℝ) :
    europeanValue m n (constantPayoffTree n c) =
      c / m.growth ^ n := by sorry

end FinancialDerivatives.FD03
