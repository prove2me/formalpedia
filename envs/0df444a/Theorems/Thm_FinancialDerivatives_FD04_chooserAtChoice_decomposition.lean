-- Prove2me | Theorems.Thm_FinancialDerivatives_FD04_chooserAtChoice_decomposition
-- name    : FinancialDerivatives.FD04.chooserAtChoice_decomposition
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T10:49:41.091858+00:00
-- url     : https://prove2.me/theorems/b9c59f76-c5c6-4ccc-a01e-0ee21cdcd748
-- title:
--   Chooser decision-date decomposition
-- statement:
--   The chooser value at decision time equals the remaining-maturity call plus an immediately exercisable put on spot with strike K/R^n.
-- source:
--   Wilmott, Howison and Dewynne (1995), The Mathematics of Financial Derivatives, Chapter 11, printed pp. 197–205, especially §§11.2–11.4. Original discrete-binomial formalisation.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd04_chooserAtChoice
import Definitions.Def_fd04_callAtChoice
import Definitions.Def_fd04_putPayoff
import Definitions.Def_fd04_discountedStrike

namespace FinancialDerivatives.FD04
open FinancialDerivatives.FD03

theorem chooserAtChoice_decomposition (m : BinomialMarket)
    (K spot : ℝ) (n : ℕ) :
    chooserAtChoice m K n spot =
      callAtChoice m K n spot +
      putPayoff (discountedStrike m K n) spot := by sorry

end FinancialDerivatives.FD04
