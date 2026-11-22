-- Prove2me | Theorems.Thm_Csg_rpsSteps_fixed
-- name    : Csg.rpsSteps_fixed
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:21:21.091837+00:00
-- url     : https://prove2.me/theorems/e37d7166-6056-4924-ae19-d9021fc2b452
-- title:
--   Csg: rps Steps fixed
-- statement:
--   **The payoff, part 1.** `rpsSteps` is an exact fixed point of `rpsStepsStep`. `win1`/`win2`
--       close by `rfl` alone -- `rpsStepsStep`'s own absorbing branch pins them to `0` regardless of
--       the continuation, matching `rpsSteps`'s own `0` there with no further reasoning needed.
--       `initial`/`draw` `change` past the concrete `if` (a pure defeq jump on a closed, decidable
--       condition, the same technique `RockPaperScissorsLfp.lean` uses) down to
--       the bare stage-value equation, then close with the lemmas above plus arithmetic.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissorsSteps.lean#L202-L214
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissorsSteps.lean#L202-L214

import Definitions.Def_Csg_RockPaperScissors
import Definitions.Def_Csg_RewardUntilCertificate
import Definitions.Def_Csg_RockPaperScissorsSteps
set_option autoImplicit true
open Csg

theorem Csg.rpsSteps_fixed : rpsStepsStep rpsSteps = rpsSteps := by sorry
