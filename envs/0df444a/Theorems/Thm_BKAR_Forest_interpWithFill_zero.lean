-- Prove2me | Theorems.Thm_BKAR_Forest_interpWithFill_zero
-- name    : BKAR.Forest.interpWithFill_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:17:19.426165+00:00
-- url     : https://prove2.me/theorems/77715d60-d480-5228-9b61-75677a384e47
-- title:
--   Forest: interp With Fill zero
-- statement:
--   The Forest construction uses the interp With Fill zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Interpolation.lean#L143-L145
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Interpolation.lean#L143-L145

import Mathlib.Data.Real.Basic
import Definitions.Def_BKAR_Forest
import Definitions.Def_BKAR_Interpolation
set_option autoImplicit false
open BKAR
variable {V : Type*} [DecidableEq V]
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.interpWithFill_zero (F : Forest V) (u : F.EdgeParam → ℝ) :
    F.interpWithFill u 0 = F.standardInterp u := by sorry
