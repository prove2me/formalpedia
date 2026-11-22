-- Prove2me | Theorems.Thm_Csg_rpsCSG_reachBounded_win2
-- name    : Csg.rpsCSG_reachBounded_win2
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:18:13.849776+00:00
-- url     : https://prove2.me/theorems/24c0aa57-ecf3-4a9b-a468-7d80f5eb853a
-- title:
--   Csg: rps CSG reach Bounded win2
-- statement:
--   `win2` is worth `1` at every step budget -- direct from `reachBounded_of_goal`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissors.lean#L280-L281
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissors.lean#L280-L281

import Definitions.Def_Csg_BoundedReachability
import Definitions.Def_Csg_MatchingPennies
import Definitions.Def_Csg_RockPaperScissors
set_option autoImplicit true
open Csg

theorem Csg.rpsCSG_reachBounded_win2 (k : ℕ) : rpsCSG.reachBounded rpsGoalWin2 k .win2 = 1 := by sorry
