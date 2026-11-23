-- Prove2me | Theorems.Thm_Csg_rpsCSGSteps_stageGame_initial_payoff_col
-- name    : Csg.rpsCSGSteps_stageGame_initial_payoff_col
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:21:24.026837+00:00
-- url     : https://prove2.me/theorems/5a765023-55c8-4d19-bc0c-567ff306fb7a
-- title:
--   Csg: rps CSGSteps stage Game initial payoff col
-- statement:
--   Symmetric counterpart of `rpsCSGSteps_stageGame_initial_payoff_row`, for the column player.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissorsSteps.lean#L142-L158
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissorsSteps.lean#L142-L158

import Definitions.Def_Csg_RockPaperScissors
import Definitions.Def_Csg_RewardUntilCertificate
import Definitions.Def_Csg_RockPaperScissorsSteps
set_option autoImplicit true
open Csg

theorem Csg.rpsCSGSteps_stageGame_initial_payoff_col (v : RPSState → ℝ) {q' : RPSAction → ℝ}
    (hq' : q' ∈ stdSimplex ℝ RPSAction) :
    (rpsCSGSteps.stageGame .initial v).payoff unif3 q' =
      1 + (v .win1 + v .win2 + v .draw) / 3 := by sorry
