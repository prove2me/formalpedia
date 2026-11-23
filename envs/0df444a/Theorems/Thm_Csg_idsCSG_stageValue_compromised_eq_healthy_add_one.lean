-- Prove2me | Theorems.Thm_Csg_idsCSG_stageValue_compromised_eq_healthy_add_one
-- name    : Csg.idsCSG_stageValue_compromised_eq_healthy_add_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:25:49.869841+00:00
-- url     : https://prove2.me/theorems/df04713a-1c9a-40be-a941-969f0d6be741
-- title:
--   Csg: ids CSG stage Value compromised eq healthy add one
-- statement:
--   **The general fact.** `compromised`'s stage value is always exactly `healthy`'s plus `1`, for
--       *any* continuation `v` -- `MatrixGameMonotone.lean`'s `value_add_const` (shifting every payoff
--       entry of a matrix game by a constant shifts the value by that same constant) applied to the
--       fact above. This is the real, structural reason the same mixed-strategy pair solved *both*
--       states' stage games at both `k = 1` and `k = 2` above: it was never a coincidence specific to
--       either round, it holds automatically at every stage of `bwInd`'s recursion, with no induction
--       on the round count needed to see it.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/IntrusionDetection.lean#L417-L419
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/IntrusionDetection.lean#L417-L419

import Definitions.Def_Csg_BackwardInduction
import Definitions.Def_Csg_CsgMonotone
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_IntrusionDetection
set_option autoImplicit true
open Csg

theorem Csg.idsCSG_stageValue_compromised_eq_healthy_add_one (v : IDSState → ℝ) :
    idsCSG.stageValue .compromised v = idsCSG.stageValue .healthy v + 1 := by sorry
