-- Prove2me | Theorems.Thm_FinancialDerivatives_FD03_european_add
-- name    : FinancialDerivatives.FD03.european_add
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T08:02:39.930676+00:00
-- url     : https://prove2.me/theorems/ec6a1592-57c8-4460-857d-51f5ea56f230
-- title:
--   European binomial valuation is additive in signed payoffs
-- statement:
--   The time-zero value of the pathwise sum of any two signed, same-horizon terminal claims equals the sum of their separately computed European backward-induction values.
-- source:
--   Original finite-tree linearity theorem extending Wilmott, Howison and Dewynne (1995), Chapter 10 §10.4, equation (10.16), printed p. 188.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_europeanValue
import Definitions.Def_fd03_payoffTreeZip

namespace FinancialDerivatives.FD03

theorem european_add (m : BinomialMarket) (n : ℕ)
    (x y : PayoffTree n) :
    europeanValue m n (payoffTreeZip (fun a b => a + b) n x y) =
      europeanValue m n x + europeanValue m n y := by sorry

end FinancialDerivatives.FD03
