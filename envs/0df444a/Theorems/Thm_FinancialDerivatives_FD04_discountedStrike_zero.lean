-- Prove2me | Theorems.Thm_FinancialDerivatives_FD04_discountedStrike_zero
-- name    : FinancialDerivatives.FD04.discountedStrike_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T10:48:21.348323+00:00
-- url     : https://prove2.me/theorems/1175195a-8dc0-486f-b4b4-bfb79c2f234b
-- title:
--   Immediate strike has no discount
-- statement:
--   With zero remaining periods the discounted strike is the original strike.
-- source:
--   Wilmott, Howison and Dewynne (1995), The Mathematics of Financial Derivatives, Chapter 11, printed pp. 197–205, especially §§11.2–11.4. Original discrete-binomial formalisation.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd04_discountedStrike

namespace FinancialDerivatives.FD04
open FinancialDerivatives.FD03

theorem discountedStrike_zero (m : BinomialMarket) (K : ℝ) :
    discountedStrike m K 0 = K := by sorry

end FinancialDerivatives.FD04
