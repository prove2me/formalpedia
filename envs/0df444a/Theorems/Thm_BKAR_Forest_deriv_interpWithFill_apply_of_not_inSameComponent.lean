-- Prove2me | Theorems.Thm_BKAR_Forest_deriv_interpWithFill_apply_of_not_inSameComponent
-- name    : BKAR.Forest.deriv_interpWithFill_apply_of_not_inSameComponent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:21:45.395787+00:00
-- url     : https://prove2.me/theorems/b3e5fe68-9067-464a-b0d8-2ee5d5f5b0fa
-- title:
--   Forest: deriv interp With Fill apply of not in Same Component
-- statement:
--   The Forest construction uses the deriv interp With Fill apply of not in Same Component property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Differential.lean#L142-L152
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Differential.lean#L142-L152

import Mathlib.Analysis.Calculus.Deriv.Prod
import Definitions.Def_BKAR_PartialDeriv
import Definitions.Def_BKAR_Differential
set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.deriv_interpWithFill_apply_of_not_inSameComponent (F : Forest V)
    (u : F.EdgeParam → ℝ) {e : Edge V}
    (he : ¬ F.inSameComponent e.left e.right) (t : ℝ) :
    deriv (fun s : ℝ => F.interpWithFill u s e) t = 1 := by sorry
