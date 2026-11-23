-- Prove2me | Theorems.Thm_Csg_rpsCSGSteps_stageGame_initial_payoff_row
-- name    : Csg.rpsCSGSteps_stageGame_initial_payoff_row
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:21:16.534907+00:00
-- url     : https://prove2.me/theorems/32b5d87d-b929-490b-bfd4-b19efc64f181
-- title:
--   Csg: rps CSGSteps stage Game initial payoff row
-- statement:
--   Against uniform column play, every row action pays exactly `1 + (v win1 + v win2 + v draw)/3`
--       -- `outcome_row_sum` (now public, see `RockPaperScissors.lean`'s own note) says the sum over
--       the three responses is the same constant regardless of the row action, same as
--       `rpsCSG_stageGame_initial_payoff_row`'s argument, shifted by the constant step cost.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissorsSteps.lean#L123-L139
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissorsSteps.lean#L123-L139

import Definitions.Def_Csg_RockPaperScissors
import Definitions.Def_Csg_RewardUntilCertificate
import Definitions.Def_Csg_RockPaperScissorsSteps
set_option autoImplicit true
open Csg

theorem Csg.rpsCSGSteps_stageGame_initial_payoff_row (v : RPSState → ℝ) {p' : RPSAction → ℝ}
    (hp' : p' ∈ stdSimplex ℝ RPSAction) :
    (rpsCSGSteps.stageGame .initial v).payoff p' unif3 =
      1 + (v .win1 + v .win2 + v .draw) / 3 := by sorry
