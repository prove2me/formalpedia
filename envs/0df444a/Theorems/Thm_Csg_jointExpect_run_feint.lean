-- Prove2me | Theorems.Thm_Csg_jointExpect_run_feint
-- name    : Csg.jointExpect_run_feint
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:00:31.852802+00:00
-- url     : https://prove2.me/theorems/0d47b51e-a889-4c29-9355-9e06eab8eac1
-- title:
--   Csg: joint Expect run feint
-- statement:
--   The Csg construction uses the joint Expect run feint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishFeint.lean#L266-L273
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishFeint.lean#L266-L273

import Definitions.Def_Csg_Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Definitions.Def_Csg_SkirmishFeint
set_option autoImplicit true
open Csg

theorem Csg.jointExpect_run_feint (v : SkirmishState → ℝ) :
    ∑ s', (jointK .hide .run .feint s').toReal * v s' =
      (3 / 10) * v .home + (7 / 10) * v .wet := by sorry
