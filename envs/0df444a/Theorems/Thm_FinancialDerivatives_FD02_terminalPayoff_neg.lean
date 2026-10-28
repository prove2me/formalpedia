-- Prove2me | Theorems.Thm_FinancialDerivatives_FD02_terminalPayoff_neg
-- name    : FinancialDerivatives.FD02.terminalPayoff_neg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:56:03.644279+00:00
-- url     : https://prove2.me/theorems/90ff772d-18e0-472e-a947-73ba1e364a07
-- title:
--   Opposite trades have opposite terminal payoffs
-- statement:
--   The signed opposite of a portfolio has the negative terminal value in each state.
--
--   This is an original derived theorem target; a remote compiler must validate its declaration and proof.
-- source:
--   Derived from Wilmott, Howison and Dewynne (1995), §2.4, pp. 30–31. https://doi.org/10.1017/CBO9780511812545.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd02_TwoStateMarket
import Definitions.Def_fd02_Trade
import Definitions.Def_fd02_terminalPayoff

namespace FinancialDerivatives.FD02

/-- Opposite trades have opposite terminal payoffs. -/
theorem terminalPayoff_neg (m : TwoStateMarket) (t : Trade) (ω : Bool) :
  terminalPayoff m ({ shares := -t.shares, cash := -t.cash } : Trade) ω = -terminalPayoff m t ω := by sorry

end FinancialDerivatives.FD02
