-- Prove2me | Theorems.Thm_FinancialDerivatives_FD04_discountedStrike_succ
-- name    : FinancialDerivatives.FD04.discountedStrike_succ
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T10:48:33.67401+00:00
-- url     : https://prove2.me/theorems/fee59cc5-c616-4429-a8c7-6463194dffa2
-- title:
--   Discounted-strike one-step recursion
-- statement:
--   Present-valuing one more period divides the earlier discounted amount by the bank growth R.
-- source:
--   Wilmott, Howison and Dewynne (1995), The Mathematics of Financial Derivatives, Chapter 11, printed pp. 197–205, especially §§11.2–11.4. Original discrete-binomial formalisation.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd04_discountedStrike

namespace FinancialDerivatives.FD04
open FinancialDerivatives.FD03

theorem discountedStrike_succ (m : BinomialMarket)
    (K : ℝ) (n : ℕ) :
    discountedStrike m K (n + 1) =
      discountedStrike m K n / m.growth := by sorry

end FinancialDerivatives.FD04
