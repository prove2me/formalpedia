-- Prove2me | Theorems.Thm_Csg_hiderAction_sum
-- name    : Csg.hiderAction_sum
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T21:57:22.158568+00:00
-- url     : https://prove2.me/theorems/ac90120c-a61d-4a15-9604-ef2420e4edf2
-- title:
--   Csg: hider Action sum
-- statement:
--   Expand a sum over all of `HiderAction` into its two terms, matching this project's established
--       `_sum` idiom (`Csg.ConcurrentCoBuchiExample.rowMove_sum` and others).
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishFeint.lean#L128-L131
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishFeint.lean#L128-L131

import Definitions.Def_Csg_Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Definitions.Def_Csg_SkirmishFeint
set_option autoImplicit true
open Csg

theorem Csg.hiderAction_sum {β : Type*} [AddCommMonoid β] (f : HiderAction → β) :
    ∑ a : HiderAction, f a = f .hide + f .run := by sorry
