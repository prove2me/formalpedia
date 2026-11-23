-- Prove2me | Theorems.Thm_Csg_rpsCSG_stageGame_initial_payoff_col
-- name    : Csg.rpsCSG_stageGame_initial_payoff_col
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:17:07.466026+00:00
-- url     : https://prove2.me/theorems/a8fddbf3-b411-4ed7-828f-78f97a1cabb0
-- title:
--   Csg: rps CSG stage Game initial payoff col
-- statement:
--   Symmetric counterpart of `rpsCSG_stageGame_initial_payoff_row` for the column player.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissors.lean#L226-L241
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissors.lean#L226-L241

import Definitions.Def_Csg_BoundedReachability
import Definitions.Def_Csg_MatchingPennies
import Definitions.Def_Csg_RockPaperScissors
set_option autoImplicit true
open Csg

theorem Csg.rpsCSG_stageGame_initial_payoff_col (v : RPSState → ℝ) {q' : RPSAction → ℝ}
    (hq' : q' ∈ stdSimplex ℝ RPSAction) :
    (rpsCSG.stageGame .initial v).payoff unif3 q' = (v .win1 + v .win2 + v .draw) / 3 := by sorry
