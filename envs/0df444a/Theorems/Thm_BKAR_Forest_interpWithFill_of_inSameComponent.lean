-- Prove2me | Theorems.Thm_BKAR_Forest_interpWithFill_of_inSameComponent
-- name    : BKAR.Forest.interpWithFill_of_inSameComponent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:20:21.572799+00:00
-- url     : https://prove2.me/theorems/0f665a20-947d-4311-99fc-ca511a3aecb3
-- title:
--   Forest: interp With Fill of in Same Component
-- statement:
--   The Forest construction uses the interp With Fill of in Same Component property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Differential.lean#L129-L133
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Differential.lean#L129-L133

import Mathlib.Analysis.Calculus.Deriv.Prod
import Definitions.Def_BKAR_PartialDeriv
import Definitions.Def_BKAR_Differential
set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.interpWithFill_of_inSameComponent (F : Forest V)
    (u : F.EdgeParam → ℝ) (t : ℝ) {e : Edge V}
    (he : F.inSameComponent e.left e.right) :
    F.interpWithFill u t e = F.pathMin u (F.pathInF e.left e.right he) := by sorry
