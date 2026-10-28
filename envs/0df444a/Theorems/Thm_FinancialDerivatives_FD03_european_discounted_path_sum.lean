-- Prove2me | Theorems.Thm_FinancialDerivatives_FD03_european_discounted_path_sum
-- name    : FinancialDerivatives.FD03.european_discounted_path_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T08:07:42.938653+00:00
-- url     : https://prove2.me/theorems/e63deab4-dd2a-4f85-843f-244ea3c88ff3
-- title:
--   Finite-path risk-neutral expectation equals recursive European value
-- statement:
--   For any signed claim over the complete depth-N binary tree, its backwards-induction European price equals the risk-neutral product-weighted sum of all maturity cashflows divided by R to the Nth power. The separate weighted fold has no embedded discounting, making the full-horizon discount explicit.
-- source:
--   Original full-history expectation equivalence formalising the European risk-neutral backward induction in Wilmott, Howison and Dewynne (1995), Chapter 10 §§10.2–10.4, printed pp. 182–189.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_europeanValue
import Definitions.Def_fd03_weightedPathSum

namespace FinancialDerivatives.FD03

theorem european_discounted_path_sum (m : BinomialMarket)
    (n : ℕ) (claim : PayoffTree n) :
    europeanValue m n claim =
      weightedPathSum m n claim / m.growth ^ n := by sorry

end FinancialDerivatives.FD03
