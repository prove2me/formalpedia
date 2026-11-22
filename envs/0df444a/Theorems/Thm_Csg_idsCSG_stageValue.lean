-- Prove2me | Theorems.Thm_Csg_idsCSG_stageValue
-- name    : Csg.idsCSG_stageValue
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:23:21.579802+00:00
-- url     : https://prove2.me/theorems/d205caa8-87ab-4dd9-b013-1b8ea7684009
-- title:
--   Csg: ids CSG stage Value
-- statement:
--   **The payoff.** The one-round-remaining stage-game value at either state, matching `idsV1`.
--       Same `value_unique` + shared-saddle-point argument `RockPaperScissors.lean`'s
--       `rpsCSG_stageValue_initial` uses, with `idsP`/`idsQ` in place of the uniform `unif3`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/IntrusionDetection.lean#L214-L228
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/IntrusionDetection.lean#L214-L228

import Definitions.Def_Csg_BackwardInduction
import Definitions.Def_Csg_CsgMonotone
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_IntrusionDetection
set_option autoImplicit true
open Csg

theorem Csg.idsCSG_stageValue (s : IDSState) : idsCSG.stageValue s (fun _ => 0) = idsV1 s := by sorry
