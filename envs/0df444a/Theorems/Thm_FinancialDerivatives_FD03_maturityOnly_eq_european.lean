-- Prove2me | Theorems.Thm_FinancialDerivatives_FD03_maturityOnly_eq_european
-- name    : FinancialDerivatives.FD03.maturityOnly_eq_european
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T08:03:57.525784+00:00
-- url     : https://prove2.me/theorems/c33d4ec2-944d-49d8-b79d-686860f36684
-- title:
--   Maturity-only Snell recursion equals European valuation
-- statement:
--   When early exercise is forbidden at every interior node, the finite Snell recursion applied to a stock-based reward equals the European backward-induction value of the same maturity reward on every full-history stock path.
-- source:
--   Original finite-tree European/American bridge corresponding to Wilmott, Howison and Dewynne (1995), Chapter 10 §§10.4–10.5, equations (10.16)–(10.17), printed pp. 188–191.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_europeanValue
import Definitions.Def_fd03_terminalStockTree
import Definitions.Def_fd03_payoffTreeMap
import Definitions.Def_fd03_snellValue
import Definitions.Def_fd03_exerciseStockTree

namespace FinancialDerivatives.FD03

theorem maturityOnly_eq_european (m : BinomialMarket)
    (n : ℕ) (spot : ℝ) (reward : ℝ → ℝ) :
    snellValue m n (exerciseStockTree m reward (fun _ => false) n spot) =
      europeanValue m n
        (payoffTreeMap reward n (terminalStockTree m n spot)) := by sorry

end FinancialDerivatives.FD03
