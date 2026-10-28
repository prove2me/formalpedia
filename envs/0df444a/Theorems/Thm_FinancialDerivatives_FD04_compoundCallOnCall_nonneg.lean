-- Prove2me | Theorems.Thm_FinancialDerivatives_FD04_compoundCallOnCall_nonneg
-- name    : FinancialDerivatives.FD04.compoundCallOnCall_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T10:51:05.686187+00:00
-- url     : https://prove2.me/theorems/743c5ea1-3900-41c9-81f1-f4b5871b3108
-- title:
--   Compound call payoff is nonnegative
-- statement:
--   A compound call's payment cannot be negative under the max-with-zero definition.
-- source:
--   Wilmott, Howison and Dewynne (1995), The Mathematics of Financial Derivatives, Chapter 11, printed pp. 197–205, especially §§11.2–11.4. Original discrete-binomial formalisation.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd04_compoundCallOnCallAtChoice

namespace FinancialDerivatives.FD04
open FinancialDerivatives.FD03

theorem compoundCallOnCall_nonneg (m : BinomialMarket)
    (K L spot : ℝ) (n : ℕ) :
    0 ≤ compoundCallOnCallAtChoice m K L n spot := by sorry

end FinancialDerivatives.FD04
