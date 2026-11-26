-- Prove2me | Theorems.Thm_BKAR_Forest_standardInterp_of_not_inSameComponent
-- name    : BKAR.Forest.standardInterp_of_not_inSameComponent
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:18:13.932852+00:00
-- url     : https://prove2.me/theorems/4be9b9ec-259f-5105-b901-5fa8a51ae5ac
-- title:
--   Forest: standard Interp of not in Same Component
-- statement:
--   The Forest construction uses the standard Interp of not in Same Component property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Interpolation.lean#L147-L151
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Interpolation.lean#L147-L151

import Mathlib.Data.Real.Basic
import Definitions.Def_BKAR_Forest
import Definitions.Def_BKAR_Interpolation
set_option autoImplicit false
open BKAR
variable {V : Type*} [DecidableEq V]
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.standardInterp_of_not_inSameComponent (F : Forest V)
    (u : F.EdgeParam → ℝ) {e : Edge V}
    (he : ¬ F.inSameComponent e.left e.right) :
    F.standardInterp u e = 0 := by sorry
