-- Prove2me | Theorems.Thm_Csg_idsCSG_stageGame_A
-- name    : Csg.idsCSG_stageGame_A
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:56:56.856022+00:00
-- url     : https://prove2.me/theorems/f12fa17e-53de-495f-a1ea-79e302e115f9
-- title:
--   Csg: ids CSG stage Game A
-- statement:
--   Against the all-zero continuation (`bwInd`'s base case, `rFin := fun _ => 0`), every stage
--       game's payoff matrix is exactly the immediate reward: the expected-continuation term vanishes
--       since `v ≡ 0`, regardless of what `idsK` does.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/IntrusionDetection.lean#L142-L149
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/IntrusionDetection.lean#L142-L149

import Definitions.Def_Csg_BackwardInduction
import Definitions.Def_Csg_CsgMonotone
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_IntrusionDetection
set_option autoImplicit true
open Csg

theorem Csg.idsCSG_stageGame_A (s : IDSState) (a1 : PolicyAction) (a2 : AttackAction) :
    (idsCSG.stageGame s (fun _ => 0)).A a1 a2 = idsR s a1 a2 := by sorry
