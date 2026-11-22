-- Prove2me | Theorems.Thm_Csg_rpsCSG_reachBounded_initial_zero
-- name    : Csg.rpsCSG_reachBounded_initial_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:18:55.856943+00:00
-- url     : https://prove2.me/theorems/8d01238b-ebef-4b9a-91b8-d938821decf9
-- title:
--   Csg: rps CSG reach Bounded initial zero
-- statement:
--   The Csg construction uses the rps CSG reach Bounded initial zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissors.lean#L307-L308
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissors.lean#L307-L308

import Definitions.Def_Csg_BoundedReachability
import Definitions.Def_Csg_MatchingPennies
import Definitions.Def_Csg_RockPaperScissors
set_option autoImplicit true
open Csg

theorem Csg.rpsCSG_reachBounded_initial_zero : rpsCSG.reachBounded rpsGoalWin2 0 .initial = 0 := by sorry
