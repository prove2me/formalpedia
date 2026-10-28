-- Prove2me | Theorems.Thm_FinancialDerivatives_FD05_upperKnockOut_price_antitone_monitor
-- name    : FinancialDerivatives.FD05.upperKnockOut_price_antitone_monitor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T19:42:01.973225+00:00
-- url     : https://prove2.me/theorems/60273d58-2bd6-4f4a-9227-3fc772dd3c16
-- title:
--   Additional monitoring cannot raise a knock-out value
-- statement:
--   For nonnegative terminal rewards, adding observation dates can only activate more knock-outs and weakly lower the present value.
-- source:
--   Wilmott, Howison and Dewynne (1995), The Mathematics of Financial Derivatives, Chapter 12, pp. 206–212. Rigorous finite-binomial first-hit analogue.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd05_upperKnockOutTree
import Definitions.Def_fd03_europeanValue

namespace FinancialDerivatives.FD05
open FinancialDerivatives.FD03

theorem upperKnockOut_price_antitone_monitor (m : BinomialMarket)
    (N : ℕ) (B : ℝ) (M₁ M₂ : ℕ → Bool) (g : ℝ → ℝ)
    (hM : ∀ t : ℕ, M₁ t = true → M₂ t = true)
    (hg : ∀ S : ℝ, 0 ≤ g S) :
    europeanValue m N
      (upperKnockOutTree m B M₂ g N 0 m.initialSpot false) ≤
    europeanValue m N
      (upperKnockOutTree m B M₁ g N 0 m.initialSpot false) := by sorry

end FinancialDerivatives.FD05
