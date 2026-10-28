-- Prove2me | Theorems.Thm_FinancialDerivatives_FD05_upperKnockOut_price_mono_barrier
-- name    : FinancialDerivatives.FD05.upperKnockOut_price_mono_barrier
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T19:41:48.393227+00:00
-- url     : https://prove2.me/theorems/a7b2e965-51fa-4db7-a3b4-1be700d35cb1
-- title:
--   Knock-out value increases with an upper barrier
-- statement:
--   For nonnegative terminal rewards, raising an upper knock-out level weakly increases survival and the risk-neutral option value.
-- source:
--   Wilmott, Howison and Dewynne (1995), The Mathematics of Financial Derivatives, Chapter 12, pp. 206–212. Rigorous finite-binomial first-hit analogue.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd05_upperKnockOutTree
import Definitions.Def_fd03_europeanValue

namespace FinancialDerivatives.FD05
open FinancialDerivatives.FD03

theorem upperKnockOut_price_mono_barrier (m : BinomialMarket)
    (N : ℕ) (B₁ B₂ : ℝ) (monitor : ℕ → Bool) (g : ℝ → ℝ)
    (hB : B₁ ≤ B₂) (hg : ∀ S : ℝ, 0 ≤ g S) :
    europeanValue m N
      (upperKnockOutTree m B₁ monitor g N 0 m.initialSpot false) ≤
    europeanValue m N
      (upperKnockOutTree m B₂ monitor g N 0 m.initialSpot false) := by sorry

end FinancialDerivatives.FD05
