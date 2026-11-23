-- Prove2me | Theorems.Thm_Csg_rpsCSG_untilOp_lfp_initial
-- name    : Csg.rpsCSG_untilOp_lfp_initial
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:48:29.838507+00:00
-- url     : https://prove2.me/theorems/3c3d10b1-740e-4e6e-a674-39274fb24c35
-- title:
--   Csg: rps CSG until Op lfp initial
-- statement:
--   The number itself, reconfirmed through the genuine `until` operator: `1/2`, matching
--       `rpsCSG_reachOp_lfp_initial`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissorsUntil.lean#L138-L141
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissorsUntil.lean#L138-L141

import Definitions.Def_Csg_UntilOp
import Definitions.Def_Csg_RockPaperScissorsLfp
import Definitions.Def_Csg_RockPaperScissorsUntil
set_option autoImplicit true
open Csg

theorem Csg.rpsCSG_untilOp_lfp_initial :
    ((rpsCSG.untilOp rpsSafeNotWin1 rpsGoalWin2 rpsR_zero).lfp RPSState.initial : ℝ) = 1 / 2 := by sorry
