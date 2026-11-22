-- Prove2me | Theorems.Thm_Csg_policyAction_sum
-- name    : Csg.policyAction_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:43:17.320134+00:00
-- url     : https://prove2.me/theorems/091dc111-bcdb-46c6-9dd3-8b44eccd7592
-- title:
--   Csg: policy Action sum
-- statement:
--   Expand a sum over all of `PolicyAction` into its two terms, matching `RockPaperScissors.lean`'s
--       `rpsAction_sum` idiom for the three-element case.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/IntrusionDetection.lean#L99-L102
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/IntrusionDetection.lean#L99-L102

import Definitions.Def_Csg_BackwardInduction
import Definitions.Def_Csg_CsgMonotone
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_IntrusionDetection
set_option autoImplicit true
open Csg

theorem Csg.policyAction_sum {β : Type*} [AddCommMonoid β] (f : PolicyAction → β) :
    ∑ a : PolicyAction, f a = f .defend1 + f .defend2 := by sorry
