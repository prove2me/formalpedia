-- Prove2me | Theorems.Thm_Csg_rpsCSGSteps_expect_initial
-- name    : Csg.rpsCSGSteps_expect_initial
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:21:11.754417+00:00
-- url     : https://prove2.me/theorems/18af7175-ea4c-4173-97ca-66f55fd680f0
-- title:
--   Csg: rps CSGSteps expect initial
-- statement:
--   The Csg construction uses the rps CSGSteps expect initial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissorsSteps.lean#L95-L98
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissorsSteps.lean#L95-L98

import Definitions.Def_Csg_RockPaperScissors
import Definitions.Def_Csg_RewardUntilCertificate
import Definitions.Def_Csg_RockPaperScissorsSteps
set_option autoImplicit true
open Csg

theorem Csg.rpsCSGSteps_expect_initial (a1 a2 : RPSAction) (v : RPSState → ℝ) :
    rpsCSGSteps.expect .initial a1 a2 v = v (outcome a1 a2) := by sorry
