-- Prove2me | Theorems.Thm_Csg_rpsCSGSteps_stageGame_initial_A
-- name    : Csg.rpsCSGSteps_stageGame_initial_A
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T21:56:51.121827+00:00
-- url     : https://prove2.me/theorems/d6765979-2b88-4d43-8614-5ca40b68728b
-- title:
--   Csg: rps CSGSteps stage Game initial A
-- statement:
--   The Csg construction uses the rps CSGSteps stage Game initial A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissorsSteps.lean#L112-L117
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissorsSteps.lean#L112-L117

import Definitions.Def_Csg_RockPaperScissors
import Definitions.Def_Csg_RewardUntilCertificate
import Definitions.Def_Csg_RockPaperScissorsSteps
set_option autoImplicit true
open Csg

theorem Csg.rpsCSGSteps_stageGame_initial_A (a1 a2 : RPSAction) (v : RPSState → ℝ) :
    (rpsCSGSteps.stageGame .initial v).A a1 a2 = 1 + v (outcome a1 a2) := by sorry
