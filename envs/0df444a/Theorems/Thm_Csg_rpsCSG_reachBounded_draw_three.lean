-- Prove2me | Theorems.Thm_Csg_rpsCSG_reachBounded_draw_three
-- name    : Csg.rpsCSG_reachBounded_draw_three
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:19:10.815841+00:00
-- url     : https://prove2.me/theorems/eec1fd81-bcca-4114-b955-7dadec537437
-- title:
--   Csg: rps CSG reach Bounded draw three
-- statement:
--   The Csg construction uses the rps CSG reach Bounded draw three property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissors.lean#L337-L338
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissors.lean#L337-L338

import Definitions.Def_Csg_BoundedReachability
import Definitions.Def_Csg_MatchingPennies
import Definitions.Def_Csg_RockPaperScissors
set_option autoImplicit true
open Csg

theorem Csg.rpsCSG_reachBounded_draw_three : rpsCSG.reachBounded rpsGoalWin2 3 .draw = 1 / 3 := by sorry
