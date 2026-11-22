-- Prove2me | Theorems.Thm_Csg_rpsCSG_expect_win1
-- name    : Csg.rpsCSG_expect_win1
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:16:54.896278+00:00
-- url     : https://prove2.me/theorems/1787ae0f-9365-4d97-b2c6-0d2a91d70ba0
-- title:
--   Csg: rps CSG expect win1
-- statement:
--   The Csg construction uses the rps CSG expect win1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissors.lean#L156-L159
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissors.lean#L156-L159

import Definitions.Def_Csg_BoundedReachability
import Definitions.Def_Csg_MatchingPennies
import Definitions.Def_Csg_RockPaperScissors
set_option autoImplicit true
open Csg

theorem Csg.rpsCSG_expect_win1 (a1 a2 : RPSAction) (v : RPSState → ℝ) :
    rpsCSG.expect .win1 a1 a2 v = v .win1 := by sorry
