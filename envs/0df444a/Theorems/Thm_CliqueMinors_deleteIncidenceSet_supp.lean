-- Prove2me | Theorems.Thm_CliqueMinors_deleteIncidenceSet_supp
-- name    : CliqueMinors.deleteIncidenceSet_supp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:33:41.021271+00:00
-- url     : https://prove2.me/theorems/93848e61-fb2a-50b6-a3d7-16eeaaaef44e
-- title:
--   Clique Minors: delete Incidence Set supp
-- statement:
--   The Clique Minors construction uses the delete Incidence Set supp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/CliqueMinorsLib/GraphOps.lean#L244-L249
-- source:
--   https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/CliqueMinorsLib/GraphOps.lean#L244-L249

module
public import Mathlib
public import Definitions.Def_CliqueMinorsLib_GraphOps
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open CliqueMinors
variable {V : Type*}
open scoped Classical
variable [Fintype V]
omit [Fintype V]

theorem CliqueMinors.deleteIncidenceSet_supp {G : SimpleGraph V} {S : Finset V} {v : V}
    (hsupp : ∀ a b, G.Adj a b → a ∈ S) :
    ∀ a b, (G.deleteIncidenceSet v).Adj a b → a ∈ S.erase v := by sorry
