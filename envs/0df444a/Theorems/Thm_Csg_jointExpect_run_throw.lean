-- Prove2me | Theorems.Thm_Csg_jointExpect_run_throw
-- name    : Csg.jointExpect_run_throw
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:00:36.296261+00:00
-- url     : https://prove2.me/theorems/62754d51-ef32-4b76-87c9-d7607dddbdb7
-- title:
--   Csg: joint Expect run throw
-- statement:
--   The Csg construction uses the joint Expect run throw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishFeint.lean#L262-L264
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishFeint.lean#L262-L264

import Definitions.Def_Csg_Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Definitions.Def_Csg_SkirmishFeint
set_option autoImplicit true
open Csg

theorem Csg.jointExpect_run_throw (v : SkirmishState → ℝ) :
    ∑ s', (jointK .hide .run .throw s').toReal * v s' = v .wet := by sorry
