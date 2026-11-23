-- Prove2me | Theorems.Thm_Csg_idsCSG_stageGame_compromised_eq_healthy_add_one
-- name    : Csg.idsCSG_stageGame_compromised_eq_healthy_add_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:25:27.752865+00:00
-- url     : https://prove2.me/theorems/ed8208a1-316f-41d9-b396-72b26b7ea2a6
-- title:
--   Csg: ids CSG stage Game compromised eq healthy add one
-- statement:
--   The two states' stage-game payoff matrices differ by exactly the constant `1`, at *every*
--       joint action and against *any* continuation `v` -- not just the zero continuation or `idsV1`.
--       Immediate from `idsCSG_stageGame_A'` plus the reward table's own structure (`idsR`'s
--       `compromised` row is its `healthy` row plus `1`, pointwise): the expected-continuation term is
--       identical between the two states for the same `v`, since `idsK` is state-independent, so only
--       the reward term's `+ 1` survives.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/IntrusionDetection.lean#L404-L408
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/IntrusionDetection.lean#L404-L408

import Definitions.Def_Csg_BackwardInduction
import Definitions.Def_Csg_CsgMonotone
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_IntrusionDetection
set_option autoImplicit true
open Csg

theorem Csg.idsCSG_stageGame_compromised_eq_healthy_add_one (v : IDSState → ℝ) (a1 : PolicyAction)
    (a2 : AttackAction) :
    (idsCSG.stageGame .compromised v).A a1 a2 = (idsCSG.stageGame .healthy v).A a1 a2 + 1 := by sorry
