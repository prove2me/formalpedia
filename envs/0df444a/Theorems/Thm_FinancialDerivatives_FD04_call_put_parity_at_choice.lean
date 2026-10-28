-- Prove2me | Theorems.Thm_FinancialDerivatives_FD04_call_put_parity_at_choice
-- name    : FinancialDerivatives.FD04.call_put_parity_at_choice
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T10:49:19.325848+00:00
-- url     : https://prove2.me/theorems/37a979e0-b645-4932-bd20-6a28e5dd30c8
-- title:
--   Choice-date put–call parity
-- statement:
--   For same strike K and same remaining maturity n, the option values obey call minus put equals spot minus K/R^n.
-- source:
--   Wilmott, Howison and Dewynne (1995), The Mathematics of Financial Derivatives, Chapter 11, printed pp. 197–205, especially §§11.2–11.4. Original discrete-binomial formalisation.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd04_callAtChoice
import Definitions.Def_fd04_putAtChoice
import Definitions.Def_fd04_discountedStrike

namespace FinancialDerivatives.FD04
open FinancialDerivatives.FD03

theorem call_put_parity_at_choice (m : BinomialMarket)
    (K spot : ℝ) (n : ℕ) :
    callAtChoice m K n spot - putAtChoice m K n spot =
      spot - discountedStrike m K n := by sorry

end FinancialDerivatives.FD04
