-- Prove2me | Theorems.Thm_Csg_rpsCSG_stageGame_initial_A
-- name    : Csg.rpsCSG_stageGame_initial_A
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T21:56:04.909006+00:00
-- url     : https://prove2.me/theorems/1244dad9-c35b-4c34-a041-e4c76353b340
-- title:
--   Csg: rps CSG stage Game initial A
-- statement:
--   The Csg construction uses the rps CSG stage Game initial A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissors.lean#L192-L196
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissors.lean#L192-L196

import Definitions.Def_Csg_BoundedReachability
import Definitions.Def_Csg_MatchingPennies
import Definitions.Def_Csg_RockPaperScissors
set_option autoImplicit true
open Csg

theorem Csg.rpsCSG_stageGame_initial_A (a1 a2 : RPSAction) (v : RPSState → ℝ) :
    (rpsCSG.stageGame .initial v).A a1 a2 = v (outcome a1 a2) := by sorry
