-- Prove2me | Theorems.Thm_Csg_idsCSG_expect
-- name    : Csg.idsCSG_expect
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:23:33.42855+00:00
-- url     : https://prove2.me/theorems/78c9d206-f3be-4c3e-888f-55c844561caf
-- title:
--   Csg: ids CSG expect
-- statement:
--   The expected continuation value after any joint action, for *any* continuation `v`: since
--       `idsK` is deterministic and state-independent, this is just `v` evaluated at `idsNext a1 a2`,
--       regardless of `s`. Generalises `idsCSG_stageGame_A` (that theorem's `hexpect` step, specialised
--       to `v = fun _ => 0`) to an arbitrary continuation, which the two-rounds-remaining stage game
--       (continuation `idsV1`, not the zero function) actually needs.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/IntrusionDetection.lean#L281-L284
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/IntrusionDetection.lean#L281-L284

import Definitions.Def_Csg_BackwardInduction
import Definitions.Def_Csg_CsgMonotone
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_IntrusionDetection
set_option autoImplicit true
open Csg

theorem Csg.idsCSG_expect (s : IDSState) (a1 : PolicyAction) (a2 : AttackAction) (v : IDSState → ℝ) :
    idsCSG.expect s a1 a2 v = v (idsNext a1 a2) := by sorry
