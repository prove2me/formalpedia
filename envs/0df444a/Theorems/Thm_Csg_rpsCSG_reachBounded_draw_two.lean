-- Prove2me | Theorems.Thm_Csg_rpsCSG_reachBounded_draw_two
-- name    : Csg.rpsCSG_reachBounded_draw_two
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:19:02.496652+00:00
-- url     : https://prove2.me/theorems/df51f557-33db-41fa-982f-ef8c00634e0d
-- title:
--   Csg: rps CSG reach Bounded draw two
-- statement:
--   The Csg construction uses the rps CSG reach Bounded draw two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissors.lean#L328-L329
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissors.lean#L328-L329

import Definitions.Def_Csg_BoundedReachability
import Definitions.Def_Csg_MatchingPennies
import Definitions.Def_Csg_RockPaperScissors
set_option autoImplicit true
open Csg

theorem Csg.rpsCSG_reachBounded_draw_two : rpsCSG.reachBounded rpsGoalWin2 2 .draw = 1 / 3 := by sorry
