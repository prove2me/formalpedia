-- Prove2me | Theorems.Thm_Csg_rpsCSG_stageValue_draw
-- name    : Csg.rpsCSG_stageValue_draw
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:43:15.73428+00:00
-- url     : https://prove2.me/theorems/d65c6372-a47e-4a73-acba-32cd39f9a101
-- title:
--   Csg: rps CSG stage Value draw
-- statement:
--   Symmetric counterpart of `rpsCSG_stageValue_win1` for the deterministic pass-through state
--       `draw`: its stage game is also a constant matrix, equal to `v initial`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissors.lean#L184-L190
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissors.lean#L184-L190

import Definitions.Def_Csg_BoundedReachability
import Definitions.Def_Csg_MatchingPennies
import Definitions.Def_Csg_RockPaperScissors
set_option autoImplicit true
open Csg

theorem Csg.rpsCSG_stageValue_draw (v : RPSState → ℝ) : rpsCSG.stageValue .draw v = v .initial := by sorry
