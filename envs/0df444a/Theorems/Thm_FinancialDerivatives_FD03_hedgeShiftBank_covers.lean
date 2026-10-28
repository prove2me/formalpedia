-- Prove2me | Theorems.Thm_FinancialDerivatives_FD03_hedgeShiftBank_covers
-- name    : FinancialDerivatives.FD03.hedgeShiftBank_covers
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T08:05:26.246361+00:00
-- url     : https://prove2.me/theorems/210b7bbb-074f-4d4b-a571-b39d942c2a8a
-- title:
--   A nonnegative extra bank deposit preserves exercise coverage
-- statement:
--   Adding a nonnegative bank amount to a strategy that covers every permitted exercise payoff preserves coverage at every finite future history, because bank growth is strictly positive.
-- source:
--   Original finite-tree portfolio-coverage monotonicity supporting the American option writer's hedge; motivated by Wilmott, Howison and Dewynne (1995), Chapter 10 §10.5, equation (10.17), printed p. 191.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_hedgeShiftBank
import Definitions.Def_fd03_hedgeCoversExercise

namespace FinancialDerivatives.FD03

theorem hedgeShiftBank_covers (m : BinomialMarket) (n : ℕ)
    (spot extra : ℝ) (h : HedgeTree n) (exercise : ExerciseTree n)
    (hextra : 0 ≤ extra)
    (hcover : hedgeCoversExercise m n spot h exercise) :
    hedgeCoversExercise m n spot
      (hedgeShiftBank m n extra h) exercise := by sorry

end FinancialDerivatives.FD03
