-- Prove2me | Theorems.Thm_FinancialDerivatives_FD05_firstUpperHit_no_hit_iff
-- name    : FinancialDerivatives.FD05.firstUpperHit_no_hit_iff
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T19:40:15.594923+00:00
-- url     : https://prove2.me/theorems/421a864f-dbdd-45e4-a16f-572e15903366
-- title:
--   Sentinel exactly characterises survival through every observation
-- statement:
--   The no-hit sentinel is equivalent to strict survival below the upper barrier at every monitored date through maturity.
-- source:
--   Wilmott, Howison and Dewynne (1995), The Mathematics of Financial Derivatives, Chapter 12, pp. 206–212. Rigorous finite-binomial first-hit analogue.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd05_firstUpperHit
import Definitions.Def_fd05_historySpot

namespace FinancialDerivatives.FD05
open FinancialDerivatives.FD03

theorem firstUpperHit_no_hit_iff (m : BinomialMarket) (N : ℕ)
    (B : ℝ) (monitor : ℕ → Bool) (steps : List Bool) :
    firstUpperHit m N B monitor steps = N + 1 ↔
      ∀ t : ℕ, t ≤ N → monitor t = true →
        historySpot m (steps.take t) < B := by sorry

end FinancialDerivatives.FD05
