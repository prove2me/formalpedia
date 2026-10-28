-- Prove2me | Theorems.Thm_FinancialDerivatives_FD02_initialCost_neg
-- name    : FinancialDerivatives.FD02.initialCost_neg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:55:50.95727+00:00
-- url     : https://prove2.me/theorems/5a81d147-7ac2-44c2-8cbc-8d8b37dbec5a
-- title:
--   Opposite trades have opposite costs
-- statement:
--   Shorting an existing stock-and-cash trade reverses its initial cost.
--
--   This is an original derived theorem target; a remote compiler must validate its declaration and proof.
-- source:
--   Derived from Wilmott, Howison and Dewynne (1995), §3.2, pp. 33–34. https://doi.org/10.1017/CBO9780511812545.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd02_TwoStateMarket
import Definitions.Def_fd02_Trade
import Definitions.Def_fd02_initialCost

namespace FinancialDerivatives.FD02

/-- Opposite trades have opposite costs. -/
theorem initialCost_neg (m : TwoStateMarket) (t : Trade) :
  initialCost m ({ shares := -t.shares, cash := -t.cash } : Trade) = -initialCost m t := by sorry

end FinancialDerivatives.FD02
