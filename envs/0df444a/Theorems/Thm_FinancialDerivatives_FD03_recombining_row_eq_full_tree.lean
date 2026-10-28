-- Prove2me | Theorems.Thm_FinancialDerivatives_FD03_recombining_row_eq_full_tree
-- name    : FinancialDerivatives.FD03.recombining_row_eq_full_tree
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T08:06:56.731007+00:00
-- url     : https://prove2.me/theorems/71613500-9ac8-4211-9c10-55bb6fb3134e
-- title:
--   Recombining-row European algorithm agrees with full-history valuation
-- statement:
--   For every finite maturity and payoff depending only on the terminal stock price, the price produced by the N+1-state terminal row and repeated backward-row updates equals the value computed on the full 2ᴺ-path payoff tree. This is the exact correctness theorem for the textbook's efficient recombining algorithm.
-- source:
--   Original algorithm-equivalence theorem for Wilmott, Howison and Dewynne (1995), Chapter 10 §§10.1–10.4, equation (10.16), Figure 10.4, printed pp. 180–188.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_rowToRoot
import Definitions.Def_fd03_terminalRow
import Definitions.Def_fd03_europeanValue
import Definitions.Def_fd03_payoffTreeMap
import Definitions.Def_fd03_terminalStockTree

namespace FinancialDerivatives.FD03

theorem recombining_row_eq_full_tree (m : BinomialMarket)
    (n : ℕ) (reward : ℝ → ℝ) :
    rowToRoot m n (terminalRow m n reward) =
      europeanValue m n
        (payoffTreeMap reward n (terminalStockTree m n m.initialSpot)) := by sorry

end FinancialDerivatives.FD03
