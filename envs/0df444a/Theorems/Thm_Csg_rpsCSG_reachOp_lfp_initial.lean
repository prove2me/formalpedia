-- Prove2me | Theorems.Thm_Csg_rpsCSG_reachOp_lfp_initial
-- name    : Csg.rpsCSG_reachOp_lfp_initial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:47:44.206188+00:00
-- url     : https://prove2.me/theorems/e842e578-ed9a-4bb7-81ae-f4ba46836791
-- title:
--   Csg: rps CSG reach Op lfp initial
-- statement:
--   The number the whole exercise was after: the exact infinite-horizon value of reaching `win2`
--       from `initial` under optimal play is `1/2`, matching the FMSD paper's claim and the shared
--       limit of `RockPaperScissors.lean`'s own `reachBounded` sequence
--       (`0, 1/3, 1/3, 4/9, 4/9, ...`).
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissorsLfp.lean#L160-L163
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissorsLfp.lean#L160-L163

import Definitions.Def_Csg_ReachCertificate
import Definitions.Def_Csg_RockPaperScissors
import Definitions.Def_Csg_RockPaperScissorsLfp
set_option autoImplicit true
open Csg

theorem Csg.rpsCSG_reachOp_lfp_initial :
    ((rpsCSG.reachOp rpsGoalWin2 rpsR_zero).lfp RPSState.initial : ℝ) = 1 / 2 := by sorry
