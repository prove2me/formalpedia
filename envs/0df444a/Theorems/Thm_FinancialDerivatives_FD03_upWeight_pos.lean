-- Prove2me | Theorems.Thm_FinancialDerivatives_FD03_upWeight_pos
-- name    : FinancialDerivatives.FD03.upWeight_pos
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T07:56:15.50616+00:00
-- url     : https://prove2.me/theorems/6c1e6c11-3d07-4bd5-8ddd-a757192cc90f
-- title:
--   Positive risk-neutral up weight
-- statement:
--   In a repeated binomial market satisfying 0<d<R<u, the up-state weight q=(R-d)/(u-d) is strictly positive.
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapter 10 §10.2, printed pp. 182–186. Derived positivity of the risk-neutral up weight.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_upWeight

namespace FinancialDerivatives.FD03

theorem upWeight_pos (m : BinomialMarket) :
    0 < upWeight m := by sorry

end FinancialDerivatives.FD03
