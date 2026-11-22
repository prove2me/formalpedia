-- Prove2me | Theorems.Thm_Csg_rpsCSG_expect_draw
-- name    : Csg.rpsCSG_expect_draw
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:17:06.718253+00:00
-- url     : https://prove2.me/theorems/163ec712-a3de-4683-a26d-28852d526118
-- title:
--   Csg: rps CSG expect draw
-- statement:
--   The Csg construction uses the rps CSG expect draw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissors.lean#L161-L164
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissors.lean#L161-L164

import Definitions.Def_Csg_BoundedReachability
import Definitions.Def_Csg_MatchingPennies
import Definitions.Def_Csg_RockPaperScissors
set_option autoImplicit true
open Csg

theorem Csg.rpsCSG_expect_draw (a1 a2 : RPSAction) (v : RPSState → ℝ) :
    rpsCSG.expect .draw a1 a2 v = v .initial := by sorry
