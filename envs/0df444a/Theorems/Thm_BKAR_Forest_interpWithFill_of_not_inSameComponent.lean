-- Prove2me | Theorems.Thm_BKAR_Forest_interpWithFill_of_not_inSameComponent
-- name    : BKAR.Forest.interpWithFill_of_not_inSameComponent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:18:19.817913+00:00
-- url     : https://prove2.me/theorems/127670e1-02de-5d50-8370-212446afe3f0
-- title:
--   Forest: interp With Fill of not in Same Component
-- statement:
--   The Forest construction uses the interp With Fill of not in Same Component property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Interpolation.lean#L153-L157
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Interpolation.lean#L153-L157

import Mathlib.Data.Real.Basic
import Definitions.Def_BKAR_Forest
import Definitions.Def_BKAR_Interpolation
set_option autoImplicit false
open BKAR
variable {V : Type*} [DecidableEq V]
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.interpWithFill_of_not_inSameComponent (F : Forest V)
    (u : F.EdgeParam → ℝ) (t : ℝ) {e : Edge V}
    (he : ¬ F.inSameComponent e.left e.right) :
    F.interpWithFill u t e = t := by sorry
