-- Prove2me | Theorems.Thm_Csg_rpsSteps_initial_eq_two
-- name    : Csg.rpsSteps_initial_eq_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:48:56.554567+00:00
-- url     : https://prove2.me/theorems/12fe6b9c-b177-40ed-be0e-49c649ff45c6
-- title:
--   Csg: rps Steps initial eq two
-- statement:
--   The number the whole exercise was after: from `initial`, expected `2` raw `CSG` steps until
--       someone wins a round, under uniform (optimal) play.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissorsSteps.lean#L265-L265
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissorsSteps.lean#L265-L265

import Definitions.Def_Csg_RockPaperScissors
import Definitions.Def_Csg_RewardUntilCertificate
import Definitions.Def_Csg_RockPaperScissorsSteps
set_option autoImplicit true
open Csg

theorem Csg.rpsSteps_initial_eq_two : rpsSteps RPSState.initial = 2 := by sorry
