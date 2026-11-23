-- Prove2me | Theorems.Thm_Csg_rpsCSGSteps_rewardUntilOp_unique
-- name    : Csg.rpsCSGSteps_rewardUntilOp_unique
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:48:57.479682+00:00
-- url     : https://prove2.me/theorems/74a0a8d1-ee17-46c1-ae30-f6165de414e6
-- title:
--   Csg: rps CSGSteps reward Until Op unique
-- statement:
--   **The retrofit.** `rpsSteps_fixed`/`rpsSteps_unique` are exactly the `hfixed`/`huniq`
--       `CSG.rewardUntilOp_eq_of_certificate` needs, once `rpsStepsStep`'s hard-coded absorption
--       condition is read as that combinator's `goal` parameter specialised to
--       `fun s => s = win1 ∨ s = win2` -- `rpsStepsStep` and `rpsCSGSteps.rewardUntilStep` at that
--       `goal` are the same `ite` definitionally, so no bridging lemma is needed between them.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissorsSteps.lean#L257-L261
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissorsSteps.lean#L257-L261

import Definitions.Def_Csg_RockPaperScissors
import Definitions.Def_Csg_RewardUntilCertificate
import Definitions.Def_Csg_RockPaperScissorsSteps
set_option autoImplicit true
open Csg

theorem Csg.rpsCSGSteps_rewardUntilOp_unique :
    ∃! w : RPSState → ℝ,
      rpsCSGSteps.rewardUntilStep (fun s => s = RPSState.win1 ∨ s = RPSState.win2) w = w := by sorry
