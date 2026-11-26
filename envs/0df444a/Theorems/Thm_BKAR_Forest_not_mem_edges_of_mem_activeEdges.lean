-- Prove2me | Theorems.Thm_BKAR_Forest_not_mem_edges_of_mem_activeEdges
-- name    : BKAR.Forest.not_mem_edges_of_mem_activeEdges
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:21:13.740972+00:00
-- url     : https://prove2.me/theorems/a703e3ca-5315-52a5-ad61-d76a9f37eb0f
-- title:
--   Forest: not mem edges of mem active Edges
-- statement:
--   The Forest construction uses the not mem edges of mem active Edges property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Differential.lean#L68-L72
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Differential.lean#L68-L72

import Mathlib.Analysis.Calculus.Deriv.Prod
import Definitions.Def_BKAR_PartialDeriv
import Definitions.Def_BKAR_Differential
set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.not_mem_edges_of_mem_activeEdges (F : Forest V) {e : Edge V}
    (he : e ∈ F.activeEdges) :
    e ∉ F.edges := by sorry
