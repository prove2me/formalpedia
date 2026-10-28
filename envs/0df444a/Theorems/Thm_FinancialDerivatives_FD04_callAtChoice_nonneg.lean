-- Prove2me | Theorems.Thm_FinancialDerivatives_FD04_callAtChoice_nonneg
-- name    : FinancialDerivatives.FD04.callAtChoice_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T10:51:32.368519+00:00
-- url     : https://prove2.me/theorems/05e9da15-fa1f-49c0-ab0f-56153fad8116
-- title:
--   Remaining European call price is nonnegative
-- statement:
--   The finite risk-neutral recursion preserves positivity of nonnegative terminal call payments.
-- source:
--   Wilmott, Howison and Dewynne (1995), The Mathematics of Financial Derivatives, Chapter 11, printed pp. 197–205, especially §§11.2–11.4. Original discrete-binomial formalisation.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd04_callAtChoice

namespace FinancialDerivatives.FD04
open FinancialDerivatives.FD03

theorem callAtChoice_nonneg (m : BinomialMarket)
    (K spot : ℝ) (n : ℕ) :
    0 ≤ callAtChoice m K n spot := by sorry

end FinancialDerivatives.FD04
