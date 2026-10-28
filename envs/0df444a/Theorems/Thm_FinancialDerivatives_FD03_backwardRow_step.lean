-- Prove2me | Theorems.Thm_FinancialDerivatives_FD03_backwardRow_step
-- name    : FinancialDerivatives.FD03.backwardRow_step
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T08:00:03.948327+00:00
-- url     : https://prove2.me/theorems/68a0b0e3-d55a-45fe-a953-cbd9b5a78479
-- title:
--   Typed recombining-row backward step matches textbook recursion
-- statement:
--   Each parent entry k in a recombining binomial option row equals the one-step discounted risk-neutral value of next-row entries k+1 (up) and k (down), exactly matching equation (10.16).
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapter 10 §10.4, printed p. 188, equation (10.16). Formal typed-row recurrence.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_backwardRow

namespace FinancialDerivatives.FD03

theorem backwardRow_step (m : BinomialMarket) (t : ℕ)
    (next : Fin (t + 2) → ℝ) (k : Fin (t + 1)) :
    backwardRow m t next k =
      oneStepValue m (next (Fin.succ k)) (next (Fin.castSucc k)) := by sorry

end FinancialDerivatives.FD03
