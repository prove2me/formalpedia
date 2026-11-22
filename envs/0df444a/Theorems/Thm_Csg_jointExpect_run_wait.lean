-- Prove2me | Theorems.Thm_Csg_jointExpect_run_wait
-- name    : Csg.jointExpect_run_wait
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T21:59:46.8878+00:00
-- url     : https://prove2.me/theorems/b51af45e-467f-404f-919b-328eecfd4b90
-- title:
--   Csg: joint Expect run wait
-- statement:
--   The Csg construction uses the joint Expect run wait property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishFeint.lean#L258-L260
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishFeint.lean#L258-L260

import Definitions.Def_Csg_Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Definitions.Def_Csg_SkirmishFeint
set_option autoImplicit true
open Csg

theorem Csg.jointExpect_run_wait (v : SkirmishState → ℝ) :
    ∑ s', (jointK .hide .run .wait s').toReal * v s' = v .home := by sorry
