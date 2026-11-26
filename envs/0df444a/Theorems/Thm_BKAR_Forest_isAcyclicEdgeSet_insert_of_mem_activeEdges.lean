-- Prove2me | Theorems.Thm_BKAR_Forest_isAcyclicEdgeSet_insert_of_mem_activeEdges
-- name    : BKAR.Forest.isAcyclicEdgeSet_insert_of_mem_activeEdges
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:22:53.129151+00:00
-- url     : https://prove2.me/theorems/7fa17b2d-4500-46cd-b6ce-384ea240ab0b
-- title:
--   Forest: is Acyclic Edge Set insert of mem active Edges
-- statement:
--   The Forest construction uses the is Acyclic Edge Set insert of mem active Edges property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Differential.lean#L86-L90
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Differential.lean#L86-L90

import Mathlib.Analysis.Calculus.Deriv.Prod
import Definitions.Def_BKAR_PartialDeriv
import Definitions.Def_BKAR_Differential
set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.isAcyclicEdgeSet_insert_of_mem_activeEdges (F : Forest V)
    {e : Edge V} (he : e ∈ F.activeEdges) :
    IsAcyclicEdgeSet (insert e F.edges) := by sorry
