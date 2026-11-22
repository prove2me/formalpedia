-- Prove2me | Theorems.Thm_Csg_throwerAction_sum
-- name    : Csg.throwerAction_sum
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T21:57:23.079458+00:00
-- url     : https://prove2.me/theorems/f4521dc0-30cb-4033-b776-4942f6a5c0d7
-- title:
--   Csg: thrower Action sum
-- statement:
--   Expand a sum over all of `ThrowerAction` into its three terms.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishFeint.lean#L146-L151
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishFeint.lean#L146-L151

import Definitions.Def_Csg_Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Definitions.Def_Csg_SkirmishFeint
set_option autoImplicit true
open Csg

theorem Csg.throwerAction_sum {β : Type*} [AddCommMonoid β] (f : ThrowerAction → β) :
    ∑ a : ThrowerAction, f a = f .wait + f .throw + f .feint := by sorry
