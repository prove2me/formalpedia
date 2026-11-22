-- Prove2me | Theorems.Thm_Csg_rpsCSGSteps_expect_draw
-- name    : Csg.rpsCSGSteps_expect_draw
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:21:08.590386+00:00
-- url     : https://prove2.me/theorems/ec76ca75-2ba5-4ac9-962b-fee55d4a919f
-- title:
--   Csg: rps CSGSteps expect draw
-- statement:
--   The Csg construction uses the rps CSGSteps expect draw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissorsSteps.lean#L90-L93
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissorsSteps.lean#L90-L93

import Definitions.Def_Csg_RockPaperScissors
import Definitions.Def_Csg_RewardUntilCertificate
import Definitions.Def_Csg_RockPaperScissorsSteps
set_option autoImplicit true
open Csg

theorem Csg.rpsCSGSteps_expect_draw (a1 a2 : RPSAction) (v : RPSState → ℝ) :
    rpsCSGSteps.expect .draw a1 a2 v = v .initial := by sorry
