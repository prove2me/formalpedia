-- Prove2me | Theorems.Thm_Csg_rpsCSG_reachBounded_win1
-- name    : Csg.rpsCSG_reachBounded_win1
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:17:16.920163+00:00
-- url     : https://prove2.me/theorems/63df9e3f-ae7d-4cff-bbad-37a71774b335
-- title:
--   Csg: rps CSG reach Bounded win1
-- statement:
--   `win1` is a dead end for reaching `win2`: once there, permanently worth `0`, at every step
--       budget -- direct consequence of `rpsCSG_stageValue_win1` plus induction on the budget.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissors.lean#L272-L277
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissors.lean#L272-L277

import Definitions.Def_Csg_BoundedReachability
import Definitions.Def_Csg_MatchingPennies
import Definitions.Def_Csg_RockPaperScissors
set_option autoImplicit true
open Csg

theorem Csg.rpsCSG_reachBounded_win1 (k : ℕ) : rpsCSG.reachBounded rpsGoalWin2 k .win1 = 0 := by sorry
