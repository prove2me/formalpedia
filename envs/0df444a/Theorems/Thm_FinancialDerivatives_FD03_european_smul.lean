-- Prove2me | Theorems.Thm_FinancialDerivatives_FD03_european_smul
-- name    : FinancialDerivatives.FD03.european_smul
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T08:03:01.982656+00:00
-- url     : https://prove2.me/theorems/6f32711a-ef3c-4046-8e4f-2b78a6d0f782
-- title:
--   European binomial valuation is homogeneous for signed multiples
-- statement:
--   For every real multiplier a, including negative a, valuing a claim whose terminal cashflows are all multiplied by a gives exactly a times the value of the original European claim.
-- source:
--   Original finite-tree homogeneity theorem extending Wilmott, Howison and Dewynne (1995), Chapter 10 §10.4, equation (10.16), printed p. 188.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_europeanValue
import Definitions.Def_fd03_payoffTreeMap

namespace FinancialDerivatives.FD03

theorem european_smul (m : BinomialMarket) (n : ℕ)
    (a : ℝ) (claim : PayoffTree n) :
    europeanValue m n (payoffTreeMap (fun x => a * x) n claim) =
      a * europeanValue m n claim := by sorry

end FinancialDerivatives.FD03
