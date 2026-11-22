-- Prove2me | Theorems.Thm_Csg_jointExpect_hide_feint
-- name    : Csg.jointExpect_hide_feint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:59:39.428861+00:00
-- url     : https://prove2.me/theorems/da01dbef-0dba-4347-bede-b79f9706b73f
-- title:
--   Csg: joint Expect hide feint
-- statement:
--   The Csg construction uses the joint Expect hide feint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishFeint.lean#L249-L256
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishFeint.lean#L249-L256

import Definitions.Def_Csg_Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Definitions.Def_Csg_SkirmishFeint
set_option autoImplicit true
open Csg

theorem Csg.jointExpect_hide_feint (v : SkirmishState → ℝ) :
    ∑ s', (jointK .hide .hide .feint s').toReal * v s' =
      (1 / 2) * v .home + (1 / 2) * v .wet := by sorry
