-- Prove2me | Theorems.Thm_FinancialDerivatives_FD04_compoundCallOnCall_zero_strike
-- name    : FinancialDerivatives.FD04.compoundCallOnCall_zero_strike
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T10:51:50.231466+00:00
-- url     : https://prove2.me/theorems/34bf5ed4-9f83-41a0-8be4-34a22c07c5f0
-- title:
--   Zero compound strike returns underlying call
-- statement:
--   A call-on-call with zero compound exercise strike is worth the nonnegative value of the underlying call at that date.
-- source:
--   Wilmott, Howison and Dewynne (1995), The Mathematics of Financial Derivatives, Chapter 11, printed pp. 197–205, especially §§11.2–11.4. Original discrete-binomial formalisation.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd04_compoundCallOnCallAtChoice
import Definitions.Def_fd04_callAtChoice

namespace FinancialDerivatives.FD04
open FinancialDerivatives.FD03

theorem compoundCallOnCall_zero_strike (m : BinomialMarket)
    (K spot : ℝ) (n : ℕ) :
    compoundCallOnCallAtChoice m K 0 n spot =
      callAtChoice m K n spot := by sorry

end FinancialDerivatives.FD04
