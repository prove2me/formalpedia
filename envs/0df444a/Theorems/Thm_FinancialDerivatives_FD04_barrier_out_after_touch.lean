-- Prove2me | Theorems.Thm_FinancialDerivatives_FD04_barrier_out_after_touch
-- name    : FinancialDerivatives.FD04.barrier_out_after_touch
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T10:52:28.399395+00:00
-- url     : https://prove2.me/theorems/9c974b50-14ac-48e7-87c5-d1b14964400d
-- title:
--   A touch eliminates knock-out payoff
-- statement:
--   When any supplied observation meets or exceeds the barrier, the knock-out call pays zero.
-- source:
--   Wilmott, Howison and Dewynne (1995), The Mathematics of Financial Derivatives, Chapter 11, printed pp. 197–205, especially §§11.2–11.4. Original discrete-binomial formalisation.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd04_upperBarrierTouched
import Definitions.Def_fd04_knockOutCallPayoff

namespace FinancialDerivatives.FD04

theorem barrier_out_after_touch (B K terminalSpot : ℝ)
    (observedSpots : List ℝ)
    (h : upperBarrierTouched B observedSpots = true) :
    knockOutCallPayoff B K terminalSpot observedSpots = 0 := by sorry

end FinancialDerivatives.FD04
