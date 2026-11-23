-- Prove2me | Theorems.Thm_Csg_idsCSG_stageValue_two
-- name    : Csg.idsCSG_stageValue_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:23:50.295689+00:00
-- url     : https://prove2.me/theorems/32310c0c-faa1-4b95-a2c8-6759e1b80e5f
-- title:
--   Csg: ids CSG stage Value two
-- statement:
--   **The payoff.** The two-rounds-remaining stage-game value at either state, matching `idsV2`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/IntrusionDetection.lean#L355-L369
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/IntrusionDetection.lean#L355-L369

import Definitions.Def_Csg_BackwardInduction
import Definitions.Def_Csg_CsgMonotone
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_IntrusionDetection
set_option autoImplicit true
open Csg

theorem Csg.idsCSG_stageValue_two (s : IDSState) : idsCSG.stageValue s idsV1 = idsV2 s := by sorry
