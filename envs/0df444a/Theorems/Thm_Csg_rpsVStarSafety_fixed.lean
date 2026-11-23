-- Prove2me | Theorems.Thm_Csg_rpsVStarSafety_fixed
-- name    : Csg.rpsVStarSafety_fixed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:11:18.275453+00:00
-- url     : https://prove2.me/theorems/d7fd8151-7106-4d87-a7d3-eb97f47fbe99
-- title:
--   Csg: rps VStar Safety fixed
-- statement:
--   **The payoff, part 1.** `rpsVStarSafety` is an exact fixed point of `safetyOp`: `win1`/`win2`
--       close by `rfl` alone (the concrete `¬safe` condition collapses `safetyOpFun`'s `ite` to the
--       constant `0` branch definitionally, matching both sides exactly); `initial`/`draw` reduce to
--       `RockPaperScissors.lean`'s own stage-value lemmas plus arithmetic.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissorsSafety.lean#L84-L100
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissorsSafety.lean#L84-L100

import Definitions.Def_Csg_SafetyCertificate
import Definitions.Def_Csg_RockPaperScissorsLfp
import Definitions.Def_Csg_RockPaperScissorsSafety
set_option autoImplicit true
open Csg

theorem Csg.rpsVStarSafety_fixed :
    rpsCSG.safetyOp rpsSafeUnresolved rpsR_zero rpsVStarSafety = rpsVStarSafety := by sorry
