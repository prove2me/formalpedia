-- Prove2me | Theorems.Thm_FinancialDerivatives_FD03_hedgeShiftBank_wealth
-- name    : FinancialDerivatives.FD03.hedgeShiftBank_wealth
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T08:04:59.378075+00:00
-- url     : https://prove2.me/theorems/3b24da56-b9df-4f41-9911-155457d4e5bf
-- title:
--   Bank-shifted hedge wealth increases by the cash deposit
-- statement:
--   Adding an initial real bank deposit c to a hedge increases its current wealth by exactly c at the current node, including maturity, without altering its stock holdings.
-- source:
--   Original bank-account algebra for finite self-financing strategies, conventions of Wilmott, Howison and Dewynne (1995), Chapter 10 §§10.2–10.5, printed pp. 182–191.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_hedgeShiftBank
import Definitions.Def_fd03_hedgeWealth

namespace FinancialDerivatives.FD03

theorem hedgeShiftBank_wealth (m : BinomialMarket) (n : ℕ)
    (spot extra : ℝ) (h : HedgeTree n) :
    hedgeWealth m n spot (hedgeShiftBank m n extra h) =
      hedgeWealth m n spot h + extra := by sorry

end FinancialDerivatives.FD03
