-- Prove2me | Theorems.Thm_FinancialDerivatives_FD05_emptyMonitoring_eq_vanilla
-- name    : FinancialDerivatives.FD05.emptyMonitoring_eq_vanilla
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T19:42:31.66469+00:00
-- url     : https://prove2.me/theorems/0d85ed3a-54b2-404b-9272-79a7e1b15c72
-- title:
--   No barrier observations recover vanilla pricing
-- statement:
--   When monitoring is disabled at every date, no barrier path can knock out and the contract has the vanilla European value.
-- source:
--   Wilmott, Howison and Dewynne (1995), The Mathematics of Financial Derivatives, Chapter 12, pp. 206–212. Rigorous finite-binomial first-hit analogue.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd05_upperKnockOutTree
import Definitions.Def_fd05_vanillaTerminalTree
import Definitions.Def_fd03_europeanValue

namespace FinancialDerivatives.FD05
open FinancialDerivatives.FD03

theorem emptyMonitoring_eq_vanilla (m : BinomialMarket) (N : ℕ)
    (B : ℝ) (g : ℝ → ℝ) :
    europeanValue m N
      (upperKnockOutTree m B (fun _ => false) g N 0 m.initialSpot false) =
    europeanValue m N (vanillaTerminalTree m N g) := by sorry

end FinancialDerivatives.FD05
