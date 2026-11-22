-- Prove2me | Theorems.Thm_Csg_rpsCSG_stageValue_win1
-- name    : Csg.rpsCSG_stageValue_win1
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T21:50:51.725612+00:00
-- url     : https://prove2.me/theorems/c5f87bd7-8946-4fbe-abc3-de4f0fecdb37
-- title:
--   Csg: rps CSG stage Value win1
-- statement:
--   `win1`'s stage game is a constant matrix (the transition ignores the joint action entirely),
--       so its value is that constant -- one round already in `win1`, the game is over, worth exactly
--       `v win1` forever.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissors.lean#L174-L180
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissors.lean#L174-L180

import Definitions.Def_Csg_BoundedReachability
import Definitions.Def_Csg_MatchingPennies
import Definitions.Def_Csg_RockPaperScissors
set_option autoImplicit true
open Csg

theorem Csg.rpsCSG_stageValue_win1 (v : RPSState → ℝ) : rpsCSG.stageValue .win1 v = v .win1 := by sorry
