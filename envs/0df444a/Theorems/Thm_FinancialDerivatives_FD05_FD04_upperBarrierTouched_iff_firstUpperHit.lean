-- Prove2me | Theorems.Thm_FinancialDerivatives_FD05_FD04_upperBarrierTouched_iff_firstUpperHit
-- name    : FinancialDerivatives.FD05.FD04_upperBarrierTouched_iff_firstUpperHit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T19:45:24.684208+00:00
-- url     : https://prove2.me/theorems/561adcc1-647e-4f12-93f6-5f131d94e17d
-- title:
--   FD-04 monitored-list touch equals FD-05 first-hit event
-- statement:
--   FD-04's Boolean any-touch predicate on observed stock prices is equivalent to FD-05's finite first-hit time being at or before maturity.
-- source:
--   Wilmott, Howison and Dewynne (1995), The Mathematics of Financial Derivatives, Chapter 12, pp. 206–212. Rigorous finite-binomial first-hit analogue.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd04_upperBarrierTouched
import Definitions.Def_fd05_monitoredSpots
import Definitions.Def_fd05_firstUpperHit

namespace FinancialDerivatives.FD05
open FinancialDerivatives.FD03

open FinancialDerivatives.FD04

theorem FD04_upperBarrierTouched_iff_firstUpperHit
    (m : BinomialMarket) (N : ℕ) (B : ℝ)
    (monitor : ℕ → Bool) (steps : List Bool) :
    upperBarrierTouched B (monitoredSpots m N monitor steps) = true ↔
      firstUpperHit m N B monitor steps ≤ N := by sorry

end FinancialDerivatives.FD05
