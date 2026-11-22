-- Prove2me | Theorems.Thm_Csg_jointExpect_hide_wait
-- name    : Csg.jointExpect_hide_wait
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:59:24.848132+00:00
-- url     : https://prove2.me/theorems/c3dca23a-e2aa-4f1d-ab2b-3491f4bad15f
-- title:
--   Csg: joint Expect hide wait
-- statement:
--   `s_hide`'s expected continuation value, one joint action at a time -- six cases, one per
--       `(hiderAction, throwerAction)` pair, each reused by *both* `skirmishMinCSG` and
--       `skirmishMaxCSG` below (they call `jointK .hide` with the same two arguments, just assembled
--       into the matrix in opposite row/column roles).
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishFeint.lean#L236-L238
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishFeint.lean#L236-L238

import Definitions.Def_Csg_Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Definitions.Def_Csg_SkirmishFeint
set_option autoImplicit true
open Csg

theorem Csg.jointExpect_hide_wait (v : SkirmishState → ℝ) :
    ∑ s', (jointK .hide .hide .wait s').toReal * v s' = v .hide := by sorry
