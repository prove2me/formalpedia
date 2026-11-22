-- Prove2me | Theorems.Thm_Csg_attackAction_sum
-- name    : Csg.attackAction_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:43:18.848823+00:00
-- url     : https://prove2.me/theorems/68098267-5031-47d9-ae61-d2a6c9901f68
-- title:
--   Csg: attack Action sum
-- statement:
--   Symmetric counterpart of `policyAction_sum` for `AttackAction`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/IntrusionDetection.lean#L105-L108
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/IntrusionDetection.lean#L105-L108

import Definitions.Def_Csg_BackwardInduction
import Definitions.Def_Csg_CsgMonotone
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_IntrusionDetection
set_option autoImplicit true
open Csg

theorem Csg.attackAction_sum {β : Type*} [AddCommMonoid β] (f : AttackAction → β) :
    ∑ a : AttackAction, f a = f .attack1 + f .attack2 := by sorry
