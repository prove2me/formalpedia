-- Prove2me | Theorems.Thm_Csg_rpsAction_sum
-- name    : Csg.rpsAction_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:43:18.399801+00:00
-- url     : https://prove2.me/theorems/96d0a669-41a8-4503-b908-51ee1e35d296
-- title:
--   Csg: rps Action sum
-- statement:
--   Expand a sum over all of `RPSAction` into its three terms, matching `RecyclingRobot.lean`'s
--       `robotState_sum` idiom for the two-element case. Not `private`: `RockPaperScissorsSteps.lean`
--       reuses this and the two `outcome_*_sum` facts below directly, rather than re-deriving them.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissors.lean#L87-L92
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissors.lean#L87-L92

import Definitions.Def_Csg_BoundedReachability
import Definitions.Def_Csg_MatchingPennies
import Definitions.Def_Csg_RockPaperScissors
set_option autoImplicit true
open Csg

theorem Csg.rpsAction_sum {β : Type*} [AddCommMonoid β] (f : RPSAction → β) :
    ∑ a : RPSAction, f a = f .rock + f .paper + f .scissors := by sorry
