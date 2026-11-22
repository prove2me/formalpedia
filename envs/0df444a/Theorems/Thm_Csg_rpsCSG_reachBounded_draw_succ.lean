-- Prove2me | Theorems.Thm_Csg_rpsCSG_reachBounded_draw_succ
-- name    : Csg.rpsCSG_reachBounded_draw_succ
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T21:50:37.726407+00:00
-- url     : https://prove2.me/theorems/86d0e4d2-c0d1-42df-843c-082c4760620f
-- title:
--   Csg: rps CSG reach Bounded draw succ
-- statement:
--   `draw`'s value at `k + 1` steps remaining is exactly `initial`'s value at `k` steps -- the
--       genuine extra step `draw`, as its own state, costs.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissors.lean#L285-L288
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissors.lean#L285-L288

import Definitions.Def_Csg_BoundedReachability
import Definitions.Def_Csg_MatchingPennies
import Definitions.Def_Csg_RockPaperScissors
set_option autoImplicit true
open Csg

theorem Csg.rpsCSG_reachBounded_draw_succ (k : ℕ) :
    rpsCSG.reachBounded rpsGoalWin2 (k + 1) .draw = rpsCSG.reachBounded rpsGoalWin2 k .initial := by sorry
