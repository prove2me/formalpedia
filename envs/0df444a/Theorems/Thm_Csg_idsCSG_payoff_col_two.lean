-- Prove2me | Theorems.Thm_Csg_idsCSG_payoff_col_two
-- name    : Csg.idsCSG_payoff_col_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:23:45.67281+00:00
-- url     : https://prove2.me/theorems/af609b83-1fc4-4719-8ef1-851e0211cf0f
-- title:
--   Csg: ids CSG payoff col two
-- statement:
--   Symmetric counterpart of `idsCSG_payoff_row_two` for the column player.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/IntrusionDetection.lean#L340-L352
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/IntrusionDetection.lean#L340-L352

import Definitions.Def_Csg_BackwardInduction
import Definitions.Def_Csg_CsgMonotone
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_IntrusionDetection
set_option autoImplicit true
open Csg

theorem Csg.idsCSG_payoff_col_two (s : IDSState) {q' : AttackAction → ℝ}
    (hq' : q' ∈ stdSimplex ℝ AttackAction) :
    (idsCSG.stageGame s idsV1).payoff idsP2 q' = idsV2 s := by sorry
