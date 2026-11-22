-- Prove2me | Theorems.Thm_Csg_rpsCSG_reachBounded_draw_zero
-- name    : Csg.rpsCSG_reachBounded_draw_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:18:53.516494+00:00
-- url     : https://prove2.me/theorems/a7f27192-6e10-4bcf-9428-5788df084cc6
-- title:
--   Csg: rps CSG reach Bounded draw zero
-- statement:
--   The Csg construction uses the rps CSG reach Bounded draw zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissors.lean#L310-L311
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissors.lean#L310-L311

import Definitions.Def_Csg_BoundedReachability
import Definitions.Def_Csg_MatchingPennies
import Definitions.Def_Csg_RockPaperScissors
set_option autoImplicit true
open Csg

theorem Csg.rpsCSG_reachBounded_draw_zero : rpsCSG.reachBounded rpsGoalWin2 0 .draw = 0 := by sorry
