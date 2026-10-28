-- Prove2me | Theorems.Thm_FinancialDerivatives_FD04_chooserAtChoice_ge_call
-- name    : FinancialDerivatives.FD04.chooserAtChoice_ge_call
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T10:50:31.029458+00:00
-- url     : https://prove2.me/theorems/34fe5e06-d1c0-42e3-a569-351106870504
-- title:
--   Chooser dominates call at the choice date
-- statement:
--   The maximum call-or-put decision value is at least the call value for every stock price.
-- source:
--   Wilmott, Howison and Dewynne (1995), The Mathematics of Financial Derivatives, Chapter 11, printed pp. 197–205, especially §§11.2–11.4. Original discrete-binomial formalisation.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd04_chooserAtChoice
import Definitions.Def_fd04_callAtChoice

namespace FinancialDerivatives.FD04
open FinancialDerivatives.FD03

theorem chooserAtChoice_ge_call (m : BinomialMarket)
    (K spot : ℝ) (n : ℕ) :
    callAtChoice m K n spot ≤ chooserAtChoice m K n spot := by sorry

end FinancialDerivatives.FD04
