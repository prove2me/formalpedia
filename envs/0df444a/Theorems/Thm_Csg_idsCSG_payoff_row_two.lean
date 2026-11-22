-- Prove2me | Theorems.Thm_Csg_idsCSG_payoff_row_two
-- name    : Csg.idsCSG_payoff_row_two
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:23:41.235809+00:00
-- url     : https://prove2.me/theorems/a5658cba-b4b3-4aff-a07c-eecc94d5f76f
-- title:
--   Csg: ids CSG payoff row two
-- statement:
--   Against `idsQ2`, every row strategy pays exactly `idsV2 s`, for the two-rounds-remaining stage
--       game (continuation `idsV1`). Same technique as `idsCSG_payoff_row`, via `idsCSG_stageGame_A'`
--       in place of `idsCSG_stageGame_A`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/IntrusionDetection.lean#L325-L337
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/IntrusionDetection.lean#L325-L337

import Definitions.Def_Csg_BackwardInduction
import Definitions.Def_Csg_CsgMonotone
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_IntrusionDetection
set_option autoImplicit true
open Csg

theorem Csg.idsCSG_payoff_row_two (s : IDSState) {p' : PolicyAction → ℝ}
    (hp' : p' ∈ stdSimplex ℝ PolicyAction) :
    (idsCSG.stageGame s idsV1).payoff p' idsQ2 = idsV2 s := by sorry
