-- Prove2me | Theorems.Thm_Csg_rpsCSG_safetyOp_gfp_initial
-- name    : Csg.rpsCSG_safetyOp_gfp_initial
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:49:33.393887+00:00
-- url     : https://prove2.me/theorems/99500fb1-4fb0-4bba-bc73-99dc28a7d619
-- title:
--   Csg: rps CSG safety Op gfp initial
-- statement:
--   The number the whole exercise was after: no strategy can keep rock-paper-scissors from
--       resolving into a decisive round forever, against an adversary -- the safety value of "the round
--       stays unresolved" is exactly `0` from `initial`, in stark contrast to `win2`'s reachability
--       value of `1/2` (`rpsCSG_reachOp_lfp_initial`, `RockPaperScissorsLfp.lean`).
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissorsSafety.lean#L153-L156
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissorsSafety.lean#L153-L156

import Definitions.Def_Csg_SafetyCertificate
import Definitions.Def_Csg_RockPaperScissorsLfp
import Definitions.Def_Csg_RockPaperScissorsSafety
set_option autoImplicit true
open Csg

theorem Csg.rpsCSG_safetyOp_gfp_initial :
    ((rpsCSG.safetyOp rpsSafeUnresolved rpsR_zero).gfp RPSState.initial : ℝ) = 0 := by sorry
