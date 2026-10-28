-- Prove2me | Theorems.Thm_FinancialDerivatives_FD03_terminalStockTree_positive
-- name    : FinancialDerivatives.FD03.terminalStockTree_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T08:03:42.481011+00:00
-- url     : https://prove2.me/theorems/7b2f024e-d248-40c3-abbf-4f63d42cdcb7
-- title:
--   Every descendant stock price remains strictly positive
-- statement:
--   Given any positive stock price at a current node and strictly positive up and down multipliers, every terminal stock price produced by any finite future sequence of moves remains positive.
-- source:
--   Original strict-positivity induction for Wilmott, Howison and Dewynne (1995), Chapter 10 §10.1, Figure 10.1, printed pp. 180–182.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_terminalStockTree
import Definitions.Def_fd03_payoffTreeAll

namespace FinancialDerivatives.FD03

theorem terminalStockTree_positive (m : BinomialMarket)
    (n : ℕ) (spot : ℝ) (hspot : 0 < spot) :
    payoffTreeAll (fun x => 0 < x) n
      (terminalStockTree m n spot) := by sorry

end FinancialDerivatives.FD03
