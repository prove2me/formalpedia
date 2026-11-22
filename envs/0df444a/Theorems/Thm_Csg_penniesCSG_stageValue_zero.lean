-- Prove2me | Theorems.Thm_Csg_penniesCSG_stageValue_zero
-- name    : Csg.penniesCSG_stageValue_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:16:23.92994+00:00
-- url     : https://prove2.me/theorems/8719e6b1-d689-44fe-9750-9ec831843dc8
-- title:
--   Csg: pennies CSG stage Value zero
-- statement:
--   **The payoff, part two.** With zero terminal reward, one step of backward induction on the
--       matching-pennies `CSG` gives exactly the matrix game's own value, `0` -- the whole stack
--       (`CSG.stageGame`, `CSG.stageValue`, `MatrixGame.value`) computes the textbook answer on a
--       concrete instance, not just something that type-checks.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/MatchingPennies.lean#L118-L137
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/MatchingPennies.lean#L118-L137

import Definitions.Def_Csg_BackwardInduction
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_MatchingPennies
set_option autoImplicit true
open Csg

theorem Csg.penniesCSG_stageValue_zero : penniesCSG.stageValue () (0 : Unit → ℝ) = 0 := by sorry
