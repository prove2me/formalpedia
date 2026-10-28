-- Prove2me | Theorems.Thm_FinancialDerivatives_FD02_terminalPayoff_add
-- name    : FinancialDerivatives.FD02.terminalPayoff_add
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:51:31.19162+00:00
-- url     : https://prove2.me/theorems/0506828b-1e32-4edb-850e-912702f33823
-- title:
--   Terminal stock-and-cash payoffs are additive
-- statement:
--   For either terminal state, combining two trades adds their terminal cash payments.
--
--   This is an original derived theorem target; a remote compiler must validate its declaration and proof.
-- source:
--   Derived from Wilmott, Howison and Dewynne (1995), §2.4, pp. 30–31. https://doi.org/10.1017/CBO9780511812545.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd02_TwoStateMarket
import Definitions.Def_fd02_Trade
import Definitions.Def_fd02_terminalPayoff

namespace FinancialDerivatives.FD02

/-- Terminal stock-and-cash payoffs are additive. -/
theorem terminalPayoff_add (m : TwoStateMarket) (a b : Trade) (ω : Bool) :
  terminalPayoff m ({ shares := a.shares + b.shares, cash := a.cash + b.cash } : Trade) ω = terminalPayoff m a ω + terminalPayoff m b ω := by sorry

end FinancialDerivatives.FD02
