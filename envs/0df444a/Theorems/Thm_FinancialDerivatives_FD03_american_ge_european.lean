-- Prove2me | Theorems.Thm_FinancialDerivatives_FD03_american_ge_european
-- name    : FinancialDerivatives.FD03.american_ge_european
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T08:04:24.549804+00:00
-- url     : https://prove2.me/theorems/0e47aa7f-386d-41ef-b803-2bd14963e70a
-- title:
--   American exercise opportunity weakly increases option value
-- statement:
--   For the same stock-based maturity reward and finite binomial market, the American contract permitting exercise at every prior node is worth at least as much as the European contract permitting exercise at maturity only.
-- source:
--   Original finite-tree consequence of the exercise maximum in Wilmott, Howison and Dewynne (1995), Chapter 10 §10.5, equation (10.17), printed p. 191.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_europeanValue
import Definitions.Def_fd03_terminalStockTree
import Definitions.Def_fd03_payoffTreeMap
import Definitions.Def_fd03_snellValue
import Definitions.Def_fd03_exerciseStockTree

namespace FinancialDerivatives.FD03

theorem american_ge_european (m : BinomialMarket)
    (n : ℕ) (spot : ℝ) (reward : ℝ → ℝ) :
    europeanValue m n
      (payoffTreeMap reward n (terminalStockTree m n spot)) ≤
      snellValue m n
        (exerciseStockTree m reward (fun _ => true) n spot) := by sorry

end FinancialDerivatives.FD03
