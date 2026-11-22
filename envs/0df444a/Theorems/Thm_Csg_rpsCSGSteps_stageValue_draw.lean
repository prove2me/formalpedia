-- Prove2me | Theorems.Thm_Csg_rpsCSGSteps_stageValue_draw
-- name    : Csg.rpsCSGSteps_stageValue_draw
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T21:56:40.156803+00:00
-- url     : https://prove2.me/theorems/a1a858e7-06bf-4de1-80c3-bdea4a440f27
-- title:
--   Csg: rps CSGSteps stage Value draw
-- statement:
--   `draw`'s stage game is a constant matrix (same as `rpsCSG_stageValue_draw`'s argument), now
--       worth `1` (this step's cost) plus `initial`'s continuation, since `draw` always passes straight
--       back to `initial`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissorsSteps.lean#L103-L110
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissorsSteps.lean#L103-L110

import Definitions.Def_Csg_RockPaperScissors
import Definitions.Def_Csg_RewardUntilCertificate
import Definitions.Def_Csg_RockPaperScissorsSteps
set_option autoImplicit true
open Csg

theorem Csg.rpsCSGSteps_stageValue_draw (v : RPSState → ℝ) :
    rpsCSGSteps.stageValue .draw v = 1 + v .initial := by sorry
