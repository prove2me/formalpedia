-- Prove2me | Theorems.Thm_Csg_skirmishState_sum
-- name    : Csg.skirmishState_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:43:31.274684+00:00
-- url     : https://prove2.me/theorems/4541f4f5-da3e-4b14-a7d9-d413ce525b33
-- title:
--   Csg: skirmish State sum
-- statement:
--   Expand a sum over all of `SkirmishState` into its three terms.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishFeint.lean#L167-L172
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishFeint.lean#L167-L172

import Definitions.Def_Csg_Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Definitions.Def_Csg_SkirmishFeint
set_option autoImplicit true
open Csg

theorem Csg.skirmishState_sum {β : Type*} [AddCommMonoid β] (f : SkirmishState → β) :
    ∑ s : SkirmishState, f s = f .hide + f .home + f .wet := by sorry
