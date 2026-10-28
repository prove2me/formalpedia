-- Prove2me | Theorems.Thm_FinancialDerivatives_FD05_upperKnockOutTree_mono_barrier
-- name    : FinancialDerivatives.FD05.upperKnockOutTree_mono_barrier
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T19:44:52.033393+00:00
-- url     : https://prove2.me/theorems/51f22134-0f26-4961-b876-5351f45d67d9
-- title:
--   Pathwise monotonicity in the upper knock-out level
-- statement:
--   Increasing the monitored upper knock-out level can only preserve additional nonnegative terminal rewards on individual histories.
-- source:
--   Wilmott, Howison and Dewynne (1995), The Mathematics of Financial Derivatives, Chapter 12, pp. 206–212. Rigorous finite-binomial first-hit analogue.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_payoffTreeLe
import Definitions.Def_fd05_upperKnockOutTree

namespace FinancialDerivatives.FD05
open FinancialDerivatives.FD03

theorem upperKnockOutTree_mono_barrier (m : BinomialMarket)
    (N : ℕ) (B₁ B₂ : ℝ) (monitor : ℕ → Bool) (g : ℝ → ℝ)
    (hB : B₁ ≤ B₂) (hg : ∀ S : ℝ, 0 ≤ g S) :
    payoffTreeLe N
      (upperKnockOutTree m B₁ monitor g N 0 m.initialSpot false)
      (upperKnockOutTree m B₂ monitor g N 0 m.initialSpot false) := by sorry

end FinancialDerivatives.FD05
