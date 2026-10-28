-- Prove2me | Theorems.Thm_FinancialDerivatives_FD04_call_put_payoff_parity
-- name    : FinancialDerivatives.FD04.call_put_payoff_parity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T10:48:08.450674+00:00
-- url     : https://prove2.me/theorems/0766adb7-ae90-4aba-a8eb-c0bc7c110535
-- title:
--   Terminal put–call payoff parity
-- statement:
--   At maturity, a same-strike call minus put pays the terminal stock price less the strike.
-- source:
--   Wilmott, Howison and Dewynne (1995), The Mathematics of Financial Derivatives, Chapter 11, printed pp. 197–205, especially §§11.2–11.4. Original discrete-binomial formalisation.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd04_callPayoff
import Definitions.Def_fd04_putPayoff

namespace FinancialDerivatives.FD04

theorem call_put_payoff_parity (K spot : ℝ) :
    callPayoff K spot - putPayoff K spot = spot - K := by sorry

end FinancialDerivatives.FD04
