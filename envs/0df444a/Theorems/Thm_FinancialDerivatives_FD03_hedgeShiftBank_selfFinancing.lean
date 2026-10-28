-- Prove2me | Theorems.Thm_FinancialDerivatives_FD03_hedgeShiftBank_selfFinancing
-- name    : FinancialDerivatives.FD03.hedgeShiftBank_selfFinancing
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T08:05:14.607889+00:00
-- url     : https://prove2.me/theorems/49b25cd0-82c3-4119-8a70-07b925bde1e2
-- title:
--   A consistent bank deposit preserves self-financing
-- statement:
--   If an adapted binomial hedge is self-financing, shifting its current bank account by any signed amount and growing that adjustment by the bank factor along both successors yields another self-financing strategy.
-- source:
--   Original self-financing invariance under a bank-account adjustment, conventions of Wilmott, Howison and Dewynne (1995), Chapter 10 §§10.2–10.5, printed pp. 182–191.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_hedgeShiftBank
import Definitions.Def_fd03_SelfFinancing

namespace FinancialDerivatives.FD03

theorem hedgeShiftBank_selfFinancing (m : BinomialMarket)
    (n : ℕ) (spot extra : ℝ) (h : HedgeTree n)
    (hsf : SelfFinancing m n spot h) :
    SelfFinancing m n spot (hedgeShiftBank m n extra h) := by sorry

end FinancialDerivatives.FD03
