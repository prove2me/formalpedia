-- Prove2me | Theorems.Thm_BKAR_Forest_deriv_interpWithFill_apply_of_mem_activeEdges
-- name    : BKAR.Forest.deriv_interpWithFill_apply_of_mem_activeEdges
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:24:48.928236+00:00
-- url     : https://prove2.me/theorems/d021d5cf-1997-490c-8d72-5efa8b2aaf51
-- title:
--   Forest: deriv interp With Fill apply of mem active Edges
-- statement:
--   The Forest construction uses the deriv interp With Fill apply of mem active Edges property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Differential.lean#L154-L159
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Differential.lean#L154-L159

import Mathlib.Analysis.Calculus.Deriv.Prod
import Definitions.Def_BKAR_PartialDeriv
import Definitions.Def_BKAR_Differential
set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.deriv_interpWithFill_apply_of_mem_activeEdges (F : Forest V)
    (u : F.EdgeParam → ℝ) {e : Edge V}
    (he : e ∈ F.activeEdges) (t : ℝ) :
    deriv (fun s : ℝ => F.interpWithFill u s e) t = 1 := by sorry
