-- Prove2me | Theorems.Thm_Csg_rpsCSG_reachBounded_initial_one
-- name    : Csg.rpsCSG_reachBounded_initial_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:18:55.332039+00:00
-- url     : https://prove2.me/theorems/4bc668f8-dfc2-45da-8ca5-a448d8b86d82
-- title:
--   Csg: rps CSG reach Bounded initial one
-- statement:
--   **The payoff.** `x_1 = 1/3`: within one step, `win2` is reached exactly when the very first
--       round is won outright, which under optimal (uniform) play happens with probability `1/3`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissors.lean#L315-L317
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissors.lean#L315-L317

import Definitions.Def_Csg_BoundedReachability
import Definitions.Def_Csg_MatchingPennies
import Definitions.Def_Csg_RockPaperScissors
set_option autoImplicit true
open Csg

theorem Csg.rpsCSG_reachBounded_initial_one : rpsCSG.reachBounded rpsGoalWin2 1 .initial = 1 / 3 := by sorry
