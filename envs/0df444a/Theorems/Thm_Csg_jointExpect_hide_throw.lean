-- Prove2me | Theorems.Thm_Csg_jointExpect_hide_throw
-- name    : Csg.jointExpect_hide_throw
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:59:34.808011+00:00
-- url     : https://prove2.me/theorems/e9c5a6da-fa2c-4208-a13d-80bbad5b387d
-- title:
--   Csg: joint Expect hide throw
-- statement:
--   The Csg construction uses the joint Expect hide throw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishFeint.lean#L240-L247
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishFeint.lean#L240-L247

import Definitions.Def_Csg_Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Definitions.Def_Csg_SkirmishFeint
set_option autoImplicit true
open Csg

theorem Csg.jointExpect_hide_throw (v : SkirmishState → ℝ) :
    ∑ s', (jointK .hide .hide .throw s').toReal * v s' =
      (4 / 5) * v .home + (1 / 5) * v .wet := by sorry
