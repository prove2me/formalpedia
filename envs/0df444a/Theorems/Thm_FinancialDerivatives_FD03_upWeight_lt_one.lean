-- Prove2me | Theorems.Thm_FinancialDerivatives_FD03_upWeight_lt_one
-- name    : FinancialDerivatives.FD03.upWeight_lt_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T07:56:24.580133+00:00
-- url     : https://prove2.me/theorems/f2918f1b-42f4-404e-85c9-0a8800ee29f6
-- title:
--   Risk-neutral up weight is below one
-- statement:
--   Under 0<d<R<u the market-implied up-state risk-neutral weight is strictly smaller than 1.
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapter 10 §10.2, printed pp. 182–186. Derived strict positivity of both risk-neutral weights.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_upWeight

namespace FinancialDerivatives.FD03

theorem upWeight_lt_one (m : BinomialMarket) :
    upWeight m < 1 := by sorry

end FinancialDerivatives.FD03
