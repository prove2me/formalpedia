-- Prove2me | Theorems.Thm_FinancialDerivatives_FD05_upperKnockOutTree_le_vanilla
-- name    : FinancialDerivatives.FD05.upperKnockOutTree_le_vanilla
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T19:44:41.416981+00:00
-- url     : https://prove2.me/theorems/1b85b35a-8c66-4e94-96ed-153a391fd194
-- title:
--   Pathwise nonnegative knock-out claim is below vanilla
-- statement:
--   A nonnegative terminal reward is either retained or extinguished by an upper knock-out barrier, so the payoff is pathwise bounded by vanilla.
-- source:
--   Wilmott, Howison and Dewynne (1995), The Mathematics of Financial Derivatives, Chapter 12, pp. 206–212. Rigorous finite-binomial first-hit analogue.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_payoffTreeLe
import Definitions.Def_fd05_upperKnockOutTree
import Definitions.Def_fd05_vanillaTerminalTree

namespace FinancialDerivatives.FD05
open FinancialDerivatives.FD03

theorem upperKnockOutTree_le_vanilla (m : BinomialMarket)
    (N : ℕ) (B : ℝ) (monitor : ℕ → Bool) (g : ℝ → ℝ)
    (hg : ∀ S : ℝ, 0 ≤ g S) :
    payoffTreeLe N (upperKnockOutTree m B monitor g N 0 m.initialSpot false) (vanillaTerminalTree m N g) := by sorry

end FinancialDerivatives.FD05
