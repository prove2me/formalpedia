-- Prove2me | Theorems.Thm_FinancialDerivatives_FD04_barrier_in_out_parity
-- name    : FinancialDerivatives.FD04.barrier_in_out_parity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T10:52:01.917564+00:00
-- url     : https://prove2.me/theorems/0ce336db-eb13-40d7-bfb8-a383425d103e
-- title:
--   Upper-barrier in/out payoff parity
-- statement:
--   With common monitoring and zero rebates, a knock-in and knock-out call exhaust the ordinary call payoff at maturity.
-- source:
--   Wilmott, Howison and Dewynne (1995), The Mathematics of Financial Derivatives, Chapter 11, printed pp. 197–205, especially §§11.2–11.4. Original discrete-binomial formalisation.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd04_knockInCallPayoff
import Definitions.Def_fd04_knockOutCallPayoff
import Definitions.Def_fd04_callPayoff

namespace FinancialDerivatives.FD04

theorem barrier_in_out_parity (B K terminalSpot : ℝ)
    (observedSpots : List ℝ) :
    knockInCallPayoff B K terminalSpot observedSpots +
      knockOutCallPayoff B K terminalSpot observedSpots =
      callPayoff K terminalSpot := by sorry

end FinancialDerivatives.FD04
