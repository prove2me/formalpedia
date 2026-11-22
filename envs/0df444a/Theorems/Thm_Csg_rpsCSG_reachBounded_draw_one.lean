-- Prove2me | Theorems.Thm_Csg_rpsCSG_reachBounded_draw_one
-- name    : Csg.rpsCSG_reachBounded_draw_one
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:18:59.280361+00:00
-- url     : https://prove2.me/theorems/b907b03b-cace-4f4b-8b4c-09254fcf71e7
-- title:
--   Csg: rps CSG reach Bounded draw one
-- statement:
--   The Csg construction uses the rps CSG reach Bounded draw one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissors.lean#L319-L320
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissors.lean#L319-L320

import Definitions.Def_Csg_BoundedReachability
import Definitions.Def_Csg_MatchingPennies
import Definitions.Def_Csg_RockPaperScissors
set_option autoImplicit true
open Csg

theorem Csg.rpsCSG_reachBounded_draw_one : rpsCSG.reachBounded rpsGoalWin2 1 .draw = 0 := by sorry
