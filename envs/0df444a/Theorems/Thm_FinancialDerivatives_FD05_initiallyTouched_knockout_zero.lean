-- Prove2me | Theorems.Thm_FinancialDerivatives_FD05_initiallyTouched_knockout_zero
-- name    : FinancialDerivatives.FD05.initiallyTouched_knockout_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T19:43:00.43415+00:00
-- url     : https://prove2.me/theorems/c5df72d7-bef3-4d22-a866-3e3fa8763df0
-- title:
--   Monitored inception barrier causes immediate extinction
-- statement:
--   If inception is monitored and the initial stock already reaches the upper level, every terminal knock-out claim pays zero.
-- source:
--   Wilmott, Howison and Dewynne (1995), The Mathematics of Financial Derivatives, Chapter 12, pp. 206–212. Rigorous finite-binomial first-hit analogue.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd05_upperKnockOutTree
import Definitions.Def_fd03_europeanValue

namespace FinancialDerivatives.FD05
open FinancialDerivatives.FD03

theorem initiallyTouched_knockout_zero (m : BinomialMarket) (N : ℕ)
    (B : ℝ) (monitor : ℕ → Bool) (g : ℝ → ℝ)
    (hM : monitor 0 = true) (hB : B ≤ m.initialSpot) :
    europeanValue m N
      (upperKnockOutTree m B monitor g N 0 m.initialSpot false) = 0 := by sorry

end FinancialDerivatives.FD05
