-- Prove2me | Theorems.Thm_BKAR_Forest_hasDerivAt_interpWithFill_apply_of_not_mem_activeEdges
-- name    : BKAR.Forest.hasDerivAt_interpWithFill_apply_of_not_mem_activeEdges
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:21:46.162816+00:00
-- url     : https://prove2.me/theorems/159062c3-18a8-5a1d-b572-8348045201ff
-- title:
--   Forest: has Deriv At interp With Fill apply of not mem active Edges
-- statement:
--   The Forest construction uses the has Deriv At interp With Fill apply of not mem active Edges property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Differential.lean#L184-L197
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Differential.lean#L184-L197

import Mathlib.Analysis.Calculus.Deriv.Prod
import Definitions.Def_BKAR_PartialDeriv
import Definitions.Def_BKAR_Differential
set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.hasDerivAt_interpWithFill_apply_of_not_mem_activeEdges (F : Forest V)
    (u : F.EdgeParam → ℝ) {e : Edge V}
    (he : e ∉ F.activeEdges) (t : ℝ) :
    HasDerivAt (fun s : ℝ => F.interpWithFill u s e) 0 t := by sorry
