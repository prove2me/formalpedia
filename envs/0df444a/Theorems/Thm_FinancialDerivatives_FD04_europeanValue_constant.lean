-- Prove2me | Theorems.Thm_FinancialDerivatives_FD04_europeanValue_constant
-- name    : FinancialDerivatives.FD04.europeanValue_constant
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T10:49:04.541935+00:00
-- url     : https://prove2.me/theorems/47aa0437-5e2c-49fc-a7f3-26ebdf1f9754
-- title:
--   Price of a deterministic maturity payment
-- statement:
--   The value of a constant payment K at horizon n is K divided by the nth power of the bank-growth factor.
-- source:
--   Wilmott, Howison and Dewynne (1995), The Mathematics of Financial Derivatives, Chapter 11, printed pp. 197–205, especially §§11.2–11.4. Original discrete-binomial formalisation.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_europeanValue
import Definitions.Def_fd03_constantPayoffTree
import Definitions.Def_fd04_discountedStrike

namespace FinancialDerivatives.FD04
open FinancialDerivatives.FD03

theorem europeanValue_constant (m : BinomialMarket)
    (n : ℕ) (K : ℝ) :
    europeanValue m n (constantPayoffTree n K) =
      discountedStrike m K n := by sorry

end FinancialDerivatives.FD04
