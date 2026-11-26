-- Prove2me | Theorems.Thm_BKAR_Forest_acyclic_insert_iff_edge
-- name    : BKAR.Forest.acyclic_insert_iff_edge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:21:17.321507+00:00
-- url     : https://prove2.me/theorems/bedfb2d8-0ea7-44c2-9680-2a4dcff2ace4
-- title:
--   Forest: acyclic insert iff edge
-- statement:
--   The Forest construction uses the acyclic insert iff edge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Differential.lean#L74-L84
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Differential.lean#L74-L84

import Mathlib.Analysis.Calculus.Deriv.Prod
import Definitions.Def_BKAR_PartialDeriv
import Definitions.Def_BKAR_Differential
set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.acyclic_insert_iff_edge (F : Forest V) {e : Edge V}
    (he : e ∉ F.edges) :
    IsAcyclicEdgeSet (insert e F.edges) ↔
      ¬ F.inSameComponent e.left e.right := by sorry
