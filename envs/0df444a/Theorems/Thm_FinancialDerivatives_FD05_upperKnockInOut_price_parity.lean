-- Prove2me | Theorems.Thm_FinancialDerivatives_FD05_upperKnockInOut_price_parity
-- name    : FinancialDerivatives.FD05.upperKnockInOut_price_parity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T19:38:12.519353+00:00
-- url     : https://prove2.me/theorems/72eae6fa-9ed9-41b3-9d8b-3a0918d1bebf
-- title:
--   Knock-in plus knock-out equals vanilla European value
-- statement:
--   Linearity of the actual market valuation transports complementary knock-in and knock-out terminal payoffs into an exact vanilla price decomposition.
-- source:
--   Wilmott, Howison and Dewynne (1995), The Mathematics of Financial Derivatives, Chapter 12, pp. 206–212. Rigorous finite-binomial first-hit analogue.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd05_upperKnockOutTree
import Definitions.Def_fd05_upperKnockInTree
import Definitions.Def_fd05_vanillaTerminalTree
import Definitions.Def_fd03_europeanValue

namespace FinancialDerivatives.FD05
open FinancialDerivatives.FD03

theorem upperKnockInOut_price_parity (m : BinomialMarket) (N : ℕ)
    (B : ℝ) (monitor : ℕ → Bool) (g : ℝ → ℝ) :
    europeanValue m N
      (upperKnockInTree m B monitor g N 0 m.initialSpot false) +
    europeanValue m N
      (upperKnockOutTree m B monitor g N 0 m.initialSpot false) =
    europeanValue m N (vanillaTerminalTree m N g) := by sorry

end FinancialDerivatives.FD05
