-- Prove2me | Theorems.Thm_Csg_rpsCSG_stageGame_initial_payoff_row
-- name    : Csg.rpsCSG_stageGame_initial_payoff_row
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:17:18.752526+00:00
-- url     : https://prove2.me/theorems/ac2ac3f3-8188-4fa9-93da-37aad4539b0f
-- title:
--   Csg: rps CSG stage Game initial payoff row
-- statement:
--   Against the uniform column strategy, *every* row strategy pays exactly `(win1+win2+draw)/3` --
--       `outcome_row_sum` says the inner sum is this constant regardless of the row action, so the
--       outer weighted average (any weights summing to `1`) is the same constant too.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissors.lean#L208-L223
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissors.lean#L208-L223

import Definitions.Def_Csg_BoundedReachability
import Definitions.Def_Csg_MatchingPennies
import Definitions.Def_Csg_RockPaperScissors
set_option autoImplicit true
open Csg

theorem Csg.rpsCSG_stageGame_initial_payoff_row (v : RPSState → ℝ) {p' : RPSAction → ℝ}
    (hp' : p' ∈ stdSimplex ℝ RPSAction) :
    (rpsCSG.stageGame .initial v).payoff p' unif3 = (v .win1 + v .win2 + v .draw) / 3 := by sorry
