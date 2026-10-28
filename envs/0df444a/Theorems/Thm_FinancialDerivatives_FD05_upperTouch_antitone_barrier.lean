-- Prove2me | Theorems.Thm_FinancialDerivatives_FD05_upperTouch_antitone_barrier
-- name    : FinancialDerivatives.FD05.upperTouch_antitone_barrier
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T19:40:03.181231+00:00
-- url     : https://prove2.me/theorems/74842aa6-e1fb-4bda-9c09-d88dfc89f6ae
-- title:
--   Raising the upper barrier cannot create a hit
-- statement:
--   Every observed hit of a higher upper barrier is also a hit of any lower upper barrier.
-- source:
--   Wilmott, Howison and Dewynne (1995), The Mathematics of Financial Derivatives, Chapter 12, pp. 206–212. Rigorous finite-binomial first-hit analogue.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd05_upperTouch

namespace FinancialDerivatives.FD05

theorem upperTouch_antitone_barrier (B₁ B₂ S : ℝ)
    (monitor : ℕ → Bool) (t : ℕ) (hB : B₁ ≤ B₂)
    (h : upperTouch B₂ S monitor t = true) :
    upperTouch B₁ S monitor t = true := by sorry

end FinancialDerivatives.FD05
