-- Prove2me | Theorems.Thm_FinancialDerivatives_FD04_barrier_in_no_touch
-- name    : FinancialDerivatives.FD04.barrier_in_no_touch
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T10:52:16.471955+00:00
-- url     : https://prove2.me/theorems/c9f16fde-6044-46fc-aaed-9ff1ab0d7dad
-- title:
--   No touch eliminates knock-in payoff
-- statement:
--   When every supplied observation is below the barrier, the knock-in call pays zero.
-- source:
--   Wilmott, Howison and Dewynne (1995), The Mathematics of Financial Derivatives, Chapter 11, printed pp. 197–205, especially §§11.2–11.4. Original discrete-binomial formalisation.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd04_upperBarrierTouched
import Definitions.Def_fd04_knockInCallPayoff

namespace FinancialDerivatives.FD04

theorem barrier_in_no_touch (B K terminalSpot : ℝ)
    (observedSpots : List ℝ)
    (h : upperBarrierTouched B observedSpots = false) :
    knockInCallPayoff B K terminalSpot observedSpots = 0 := by sorry

end FinancialDerivatives.FD04
