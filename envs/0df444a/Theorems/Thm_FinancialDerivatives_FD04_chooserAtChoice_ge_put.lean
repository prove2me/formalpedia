-- Prove2me | Theorems.Thm_FinancialDerivatives_FD04_chooserAtChoice_ge_put
-- name    : FinancialDerivatives.FD04.chooserAtChoice_ge_put
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T10:50:51.605779+00:00
-- url     : https://prove2.me/theorems/e0d7cc41-a48e-4112-936c-943c76252603
-- title:
--   Chooser dominates put at the choice date
-- statement:
--   The maximum call-or-put decision value is at least the put value for every stock price.
-- source:
--   Wilmott, Howison and Dewynne (1995), The Mathematics of Financial Derivatives, Chapter 11, printed pp. 197–205, especially §§11.2–11.4. Original discrete-binomial formalisation.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd04_chooserAtChoice
import Definitions.Def_fd04_putAtChoice

namespace FinancialDerivatives.FD04
open FinancialDerivatives.FD03

theorem chooserAtChoice_ge_put (m : BinomialMarket)
    (K spot : ℝ) (n : ℕ) :
    putAtChoice m K n spot ≤ chooserAtChoice m K n spot := by sorry

end FinancialDerivatives.FD04
