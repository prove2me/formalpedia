-- Prove2me | Theorems.Thm_BKAR_Forest_hasDerivAt_interpWithFill_apply_of_mem_activeEdges
-- name    : BKAR.Forest.hasDerivAt_interpWithFill_apply_of_mem_activeEdges
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:21:50.624189+00:00
-- url     : https://prove2.me/theorems/2ad73d47-4d1d-4e0f-951b-491560dbcb34
-- title:
--   Forest: has Deriv At interp With Fill apply of mem active Edges
-- statement:
--   The Forest construction uses the has Deriv At interp With Fill apply of mem active Edges property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Differential.lean#L173-L182
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Differential.lean#L173-L182

import Mathlib.Analysis.Calculus.Deriv.Prod
import Definitions.Def_BKAR_PartialDeriv
import Definitions.Def_BKAR_Differential
set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.hasDerivAt_interpWithFill_apply_of_mem_activeEdges (F : Forest V)
    (u : F.EdgeParam → ℝ) {e : Edge V}
    (he : e ∈ F.activeEdges) (t : ℝ) :
    HasDerivAt (fun s : ℝ => F.interpWithFill u s e) 1 t := by sorry
