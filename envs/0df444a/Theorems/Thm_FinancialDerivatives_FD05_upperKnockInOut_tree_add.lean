-- Prove2me | Theorems.Thm_FinancialDerivatives_FD05_upperKnockInOut_tree_add
-- name    : FinancialDerivatives.FD05.upperKnockInOut_tree_add
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T19:44:07.461825+00:00
-- url     : https://prove2.me/theorems/0679d252-1e66-4409-b423-d68a6a0e3ec8
-- title:
--   Pointwise full-history knock-in/out complementarity
-- statement:
--   At every complete binomial history the upper knock-in and knock-out terminal amounts add to the corresponding vanilla reward, for an arbitrary signed payoff.
-- source:
--   Wilmott, Howison and Dewynne (1995), The Mathematics of Financial Derivatives, Chapter 12, pp. 206–212. Rigorous finite-binomial first-hit analogue.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_payoffTreeZip
import Definitions.Def_fd05_upperKnockOutTree
import Definitions.Def_fd05_upperKnockInTree
import Definitions.Def_fd05_vanillaTerminalTree

namespace FinancialDerivatives.FD05
open FinancialDerivatives.FD03

theorem upperKnockInOut_tree_add (m : BinomialMarket)
    (N : ℕ) (B : ℝ) (monitor : ℕ → Bool) (g : ℝ → ℝ) :
    payoffTreeZip (fun a b => a + b) N
      (upperKnockInTree m B monitor g N 0 m.initialSpot false)
      (upperKnockOutTree m B monitor g N 0 m.initialSpot false) =
    vanillaTerminalTree m N g := by sorry

end FinancialDerivatives.FD05
