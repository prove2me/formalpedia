-- Prove2me | Theorems.Thm_Csg_rpsCSG_reachBounded_initial_succ
-- name    : Csg.rpsCSG_reachBounded_initial_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:18:44.68727+00:00
-- url     : https://prove2.me/theorems/fc6ca946-bfce-493d-b24d-778500eee93c
-- title:
--   Csg: rps CSG reach Bounded initial succ
-- statement:
--   The general one-step recursion at `initial`, with `win2`'s constant value already substituted
--       in -- `win1`'s constant `0` is substituted next, in `rpsCSG_reachBounded_initial_succ'`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissors.lean#L292-L297
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissors.lean#L292-L297

import Definitions.Def_Csg_BoundedReachability
import Definitions.Def_Csg_MatchingPennies
import Definitions.Def_Csg_RockPaperScissors
set_option autoImplicit true
open Csg

theorem Csg.rpsCSG_reachBounded_initial_succ (k : ℕ) :
    rpsCSG.reachBounded rpsGoalWin2 (k + 1) .initial =
      (rpsCSG.reachBounded rpsGoalWin2 k .win1 + 1 +
        rpsCSG.reachBounded rpsGoalWin2 k .draw) / 3 := by sorry
