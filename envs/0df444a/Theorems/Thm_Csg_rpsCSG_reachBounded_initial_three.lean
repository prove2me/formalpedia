-- Prove2me | Theorems.Thm_Csg_rpsCSG_reachBounded_initial_three
-- name    : Csg.rpsCSG_reachBounded_initial_three
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:33:09.973235+00:00
-- url     : https://prove2.me/theorems/82b5e480-84f3-4bf6-bd3f-c41867379a24
-- title:
--   Csg: rps CSG reach Bounded initial three
-- statement:
--   `x_3 = 4/9`: the first budget at which a resolved draw (from step `1`) can pay off.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissors.lean#L332-L335
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissors.lean#L332-L335

import Definitions.Def_Csg_BoundedReachability
import Definitions.Def_Csg_MatchingPennies
import Definitions.Def_Csg_RockPaperScissors
set_option autoImplicit true
open Csg

theorem Csg.rpsCSG_reachBounded_initial_three :
    rpsCSG.reachBounded rpsGoalWin2 3 .initial = 4 / 9 := by sorry
