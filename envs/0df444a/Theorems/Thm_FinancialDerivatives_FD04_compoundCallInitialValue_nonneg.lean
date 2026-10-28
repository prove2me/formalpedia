-- Prove2me | Theorems.Thm_FinancialDerivatives_FD04_compoundCallInitialValue_nonneg
-- name    : FinancialDerivatives.FD04.compoundCallInitialValue_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T10:52:42.516067+00:00
-- url     : https://prove2.me/theorems/1d21459b-7a90-4155-9b36-9f0991bdacca
-- title:
--   Compound call inception price is nonnegative
-- statement:
--   For every finite compound and underlying horizon, the nonnegative exercise payoff has a nonnegative inception value under strictly positive risk-neutral weights.
-- source:
--   Wilmott, Howison and Dewynne (1995), The Mathematics of Financial Derivatives, Chapter 11, printed pp. 197–205, especially §§11.2–11.4. Original discrete-binomial formalisation.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd04_compoundCallInitialValue

namespace FinancialDerivatives.FD04
open FinancialDerivatives.FD03

theorem compoundCallInitialValue_nonneg (m : BinomialMarket)
    (K L : ℝ) (exerciseSteps postExerciseSteps : ℕ) :
    0 ≤ compoundCallInitialValue m K L exerciseSteps postExerciseSteps := by sorry

end FinancialDerivatives.FD04
