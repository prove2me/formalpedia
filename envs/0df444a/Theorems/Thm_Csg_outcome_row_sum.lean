-- Prove2me | Theorems.Thm_Csg_outcome_row_sum
-- name    : Csg.outcome_row_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:55:31.700723+00:00
-- url     : https://prove2.me/theorems/bac1e373-e730-440e-8eb3-c629488585f4
-- title:
--   Csg: outcome row sum
-- statement:
--   For any fixed row action, the three possible column responses realise `win1`, `win2`, and
--       `draw` exactly once each -- the concrete fact underlying "uniform is optimal here", the same
--       role the vanishing row/column sums played for matching pennies. Not `private`: reused directly
--       by `RockPaperScissorsSteps.lean`'s own uniform-strategy argument for a different (reward-1)
--       stage game over the same `outcome` structure.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissors.lean#L126-L129
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissors.lean#L126-L129

import Definitions.Def_Csg_BoundedReachability
import Definitions.Def_Csg_MatchingPennies
import Definitions.Def_Csg_RockPaperScissors
set_option autoImplicit true
open Csg

theorem Csg.outcome_row_sum (a1 : RPSAction) (v : RPSState → ℝ) :
    v (outcome a1 .rock) + v (outcome a1 .paper) + v (outcome a1 .scissors) =
      v .win1 + v .win2 + v .draw := by sorry
