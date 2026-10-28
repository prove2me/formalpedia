-- Prove2me | Theorems.Thm_FinancialDerivatives_FD05_barrier_first_hit_valuation
-- name    : FinancialDerivatives.FD05.barrier_first_hit_valuation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T19:39:02.392999+00:00
-- url     : https://prove2.me/theorems/32b7e9db-3bf6-4bb3-ae2b-9b8a32418111
-- title:
--   MAIN GOAL: absorbing, path-sum and knock-in/out valuation identities
-- statement:
--   The central theorem derives a first-hit absorbing recursion, its discounted full-path expectation and the exact price complementarity of matched knock-in and knock-out contracts.
-- source:
--   Wilmott, Howison and Dewynne (1995), The Mathematics of Financial Derivatives, Chapter 12, pp. 206–212. Rigorous finite-binomial first-hit analogue.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd05_upperKnockOutTree
import Definitions.Def_fd05_upperKnockInTree
import Definitions.Def_fd05_upperAbsorbingValue
import Definitions.Def_fd05_discountedSurvivalPathPrice
import Definitions.Def_fd05_vanillaTerminalTree
import Definitions.Def_fd03_europeanValue

namespace FinancialDerivatives.FD05
open FinancialDerivatives.FD03

theorem barrier_first_hit_valuation (m : BinomialMarket) (N : ℕ)
    (B : ℝ) (monitor : ℕ → Bool) (g : ℝ → ℝ) :
    (upperAbsorbingValue m B monitor g N 0 m.initialSpot false =
      europeanValue m N
        (upperKnockOutTree m B monitor g N 0 m.initialSpot false)) ∧
    (europeanValue m N
      (upperKnockOutTree m B monitor g N 0 m.initialSpot false) =
      discountedSurvivalPathPrice m N B monitor g) ∧
    (europeanValue m N
      (upperKnockInTree m B monitor g N 0 m.initialSpot false) +
      europeanValue m N
        (upperKnockOutTree m B monitor g N 0 m.initialSpot false) =
      europeanValue m N (vanillaTerminalTree m N g)) := by sorry

end FinancialDerivatives.FD05
