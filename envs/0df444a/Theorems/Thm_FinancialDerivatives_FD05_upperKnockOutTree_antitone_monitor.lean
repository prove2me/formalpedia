-- Prove2me | Theorems.Thm_FinancialDerivatives_FD05_upperKnockOutTree_antitone_monitor
-- name    : FinancialDerivatives.FD05.upperKnockOutTree_antitone_monitor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T19:45:08.401771+00:00
-- url     : https://prove2.me/theorems/0f3a6df3-d5f5-411f-a0fc-800877850e77
-- title:
--   Pathwise monotonicity when monitoring dates are added
-- statement:
--   Adding observation dates can only extinguish additional histories of a nonnegative upper knock-out claim.
-- source:
--   Wilmott, Howison and Dewynne (1995), The Mathematics of Financial Derivatives, Chapter 12, pp. 206–212. Rigorous finite-binomial first-hit analogue.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_payoffTreeLe
import Definitions.Def_fd05_upperKnockOutTree

namespace FinancialDerivatives.FD05
open FinancialDerivatives.FD03

theorem upperKnockOutTree_antitone_monitor (m : BinomialMarket)
    (N : ℕ) (B : ℝ) (M₁ M₂ : ℕ → Bool) (g : ℝ → ℝ)
    (hM : ∀ t : ℕ, M₁ t = true → M₂ t = true)
    (hg : ∀ S : ℝ, 0 ≤ g S) :
    payoffTreeLe N
      (upperKnockOutTree m B M₂ g N 0 m.initialSpot false)
      (upperKnockOutTree m B M₁ g N 0 m.initialSpot false) := by sorry

end FinancialDerivatives.FD05
