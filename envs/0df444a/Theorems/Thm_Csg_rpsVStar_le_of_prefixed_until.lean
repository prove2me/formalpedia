-- Prove2me | Theorems.Thm_Csg_rpsVStar_le_of_prefixed_until
-- name    : Csg.rpsVStar_le_of_prefixed_until
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:10:25.792268+00:00
-- url     : https://prove2.me/theorems/2adef6c4-287f-4c68-a7de-761618683c8d
-- title:
--   Csg: rps VStar le of prefixed until
-- statement:
--   **The payoff, part 2.** `rpsVStar` lower-bounds every pre-fixed point of the `until` operator --
--       the *same* argument `rpsVStar_le_of_prefixed` used, unaffected by the change of operator: `win2`
--       is still forced to `1` (the `goal` branch is identical between the two operators), `win1`'s
--       membership lower bound `0` is already all `rpsVStar win1` needs (the `until` operator's own
--       dead-end pinning at `win1` gives no *additional* information beyond what `[0, 1]` membership
--       already provides), and `draw`/`initial`'s pre-fixed-point inequalities are literally the same
--       stage-game facts as before, since neither state's `safe`/`goal` status changes which branch of
--       `untilOpFun` they route through relative to `reachOpFun`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissorsUntil.lean#L88-L116
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissorsUntil.lean#L88-L116

import Definitions.Def_Csg_UntilOp
import Definitions.Def_Csg_RockPaperScissorsLfp
import Definitions.Def_Csg_RockPaperScissorsUntil
set_option autoImplicit true
open Csg

theorem Csg.rpsVStar_le_of_prefixed_until {b : RPSState → Set.Icc (0 : ℝ) 1}
    (hb : rpsCSG.untilOp rpsSafeNotWin1 rpsGoalWin2 rpsR_zero b ≤ b) : rpsVStar ≤ b := by sorry
