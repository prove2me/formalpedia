-- Prove2me | Theorems.Thm_Csg_rpsCSG_reachBounded_initial_two
-- name    : Csg.rpsCSG_reachBounded_initial_two
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:19:01.509631+00:00
-- url     : https://prove2.me/theorems/c9dfbcda-4502-439a-8d56-7adf9883ee5f
-- title:
--   Csg: rps CSG reach Bounded initial two
-- statement:
--   `x_2 = 1/3`, same as `x_1`: a second step can only help by resolving a draw, and there wasn't
--       one to resolve yet within budget `1`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissors.lean#L324-L326
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissors.lean#L324-L326

import Definitions.Def_Csg_BoundedReachability
import Definitions.Def_Csg_MatchingPennies
import Definitions.Def_Csg_RockPaperScissors
set_option autoImplicit true
open Csg

theorem Csg.rpsCSG_reachBounded_initial_two : rpsCSG.reachBounded rpsGoalWin2 2 .initial = 1 / 3 := by sorry
