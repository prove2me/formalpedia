-- Prove2me | Theorems.Thm_Csg_rpsCSGSteps_stageValue_initial
-- name    : Csg.rpsCSGSteps_stageValue_initial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:56:47.773559+00:00
-- url     : https://prove2.me/theorems/4d2856be-78df-46ea-9d81-cf967632f3c7
-- title:
--   Csg: rps CSGSteps stage Value initial
-- statement:
--   **The payoff.** `initial`'s stage-game value, for *any* continuation `v`: `1` (this step's
--       cost) plus the average of `v` at the three possible outcomes -- the same
--       `value_unique` + uniform-strategy-is-a-saddle-point argument every other stage game in this
--       line has used, unaffected by the reward shift.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissorsSteps.lean#L164-L179
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissorsSteps.lean#L164-L179

import Definitions.Def_Csg_RockPaperScissors
import Definitions.Def_Csg_RewardUntilCertificate
import Definitions.Def_Csg_RockPaperScissorsSteps
set_option autoImplicit true
open Csg

theorem Csg.rpsCSGSteps_stageValue_initial (v : RPSState → ℝ) :
    rpsCSGSteps.stageValue .initial v = 1 + (v .win1 + v .win2 + v .draw) / 3 := by sorry
