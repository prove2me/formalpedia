-- Prove2me | Theorems.Thm_FinancialDerivatives_FD04_compoundCallInitialValue_zero_strike
-- name    : FinancialDerivatives.FD04.compoundCallInitialValue_zero_strike
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T10:53:18.135105+00:00
-- url     : https://prove2.me/theorems/b75feb26-4249-4a1c-96ee-74c3ed5d6e1c
-- title:
--   Zero-strike compound call collapses to a longer call
-- statement:
--   With no additional payment at compound exercise, the inception price of the call-on-call equals the premium of the underlying vanilla call with the combined horizon.
-- source:
--   Wilmott, Howison and Dewynne (1995), The Mathematics of Financial Derivatives, Chapter 11, printed pp. 197–205, especially §§11.2–11.4. Original discrete-binomial formalisation.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd04_compoundCallInitialValue
import Definitions.Def_fd04_callInitialValue

namespace FinancialDerivatives.FD04
open FinancialDerivatives.FD03

theorem compoundCallInitialValue_zero_strike (m : BinomialMarket)
    (K : ℝ) (exerciseSteps postExerciseSteps : ℕ) :
    compoundCallInitialValue m K 0 exerciseSteps postExerciseSteps =
      callInitialValue m K (exerciseSteps + postExerciseSteps) := by sorry

end FinancialDerivatives.FD04
