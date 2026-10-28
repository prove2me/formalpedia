-- Prove2me | Theorems.Thm_FinancialDerivatives_FD05_upperKnockOut_price_bounds
-- name    : FinancialDerivatives.FD05.upperKnockOut_price_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T19:38:42.029922+00:00
-- url     : https://prove2.me/theorems/525c294d-6d61-4df9-b235-3938e65d641a
-- title:
--   Nonnegative knock-out price is bounded by vanilla price
-- statement:
--   For any nonnegative terminal reward, positive state prices place the knock-out value between zero and the otherwise identical vanilla value.
-- source:
--   Wilmott, Howison and Dewynne (1995), The Mathematics of Financial Derivatives, Chapter 12, pp. 206–212. Rigorous finite-binomial first-hit analogue.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd05_upperKnockOutTree
import Definitions.Def_fd05_vanillaTerminalTree
import Definitions.Def_fd03_europeanValue

namespace FinancialDerivatives.FD05
open FinancialDerivatives.FD03

theorem upperKnockOut_price_bounds (m : BinomialMarket) (N : ℕ)
    (B : ℝ) (monitor : ℕ → Bool) (g : ℝ → ℝ)
    (hg : ∀ S : ℝ, 0 ≤ g S) :
    0 ≤ europeanValue m N
      (upperKnockOutTree m B monitor g N 0 m.initialSpot false) ∧
    europeanValue m N
      (upperKnockOutTree m B monitor g N 0 m.initialSpot false) ≤
    europeanValue m N (vanillaTerminalTree m N g) := by sorry

end FinancialDerivatives.FD05
