-- Prove2me | Theorems.Thm_Csg_rpsCSG_expect_initial
-- name    : Csg.rpsCSG_expect_initial
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:17:07.14703+00:00
-- url     : https://prove2.me/theorems/e3ba6f9e-85e3-4da6-b969-38bb2c49aef4
-- title:
--   Csg: rps CSG expect initial
-- statement:
--   The Csg construction uses the rps CSG expect initial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissors.lean#L166-L169
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissors.lean#L166-L169

import Definitions.Def_Csg_BoundedReachability
import Definitions.Def_Csg_MatchingPennies
import Definitions.Def_Csg_RockPaperScissors
set_option autoImplicit true
open Csg

theorem Csg.rpsCSG_expect_initial (a1 a2 : RPSAction) (v : RPSState → ℝ) :
    rpsCSG.expect .initial a1 a2 v = v (outcome a1 a2) := by sorry
