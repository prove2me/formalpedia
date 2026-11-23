-- Prove2me | Theorems.Thm_Csg_rpsSteps_draw_eq_three
-- name    : Csg.rpsSteps_draw_eq_three
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:49:08.955697+00:00
-- url     : https://prove2.me/theorems/6383b83b-abba-4264-8342-ca67c88f7937
-- title:
--   Csg: rps Steps draw eq three
-- statement:
--   From `draw`, expected `3` -- the one genuine extra step `draw` costs, matching
--       `RockPaperScissors.lean`'s own observation that `draw` doubles the raw step count per round.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissorsSteps.lean#L269-L269
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissorsSteps.lean#L269-L269

import Definitions.Def_Csg_RockPaperScissors
import Definitions.Def_Csg_RewardUntilCertificate
import Definitions.Def_Csg_RockPaperScissorsSteps
set_option autoImplicit true
open Csg

theorem Csg.rpsSteps_draw_eq_three : rpsSteps RPSState.draw = 3 := by sorry
