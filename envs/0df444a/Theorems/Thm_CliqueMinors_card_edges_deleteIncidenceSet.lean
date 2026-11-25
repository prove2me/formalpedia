-- Prove2me | Theorems.Thm_CliqueMinors_card_edges_deleteIncidenceSet
-- name    : CliqueMinors.card_edges_deleteIncidenceSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:34:13.447356+00:00
-- url     : https://prove2.me/theorems/b2407c2b-688f-42cd-a122-52e8370230c3
-- title:
--   Clique Minors: card edges delete Incidence Set
-- statement:
--   The Clique Minors construction uses the card edges delete Incidence Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/CliqueMinorsLib/GraphOps.lean#L255-L265
-- source:
--   https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/CliqueMinorsLib/GraphOps.lean#L255-L265

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

theorem CliqueMinors.card_edges_deleteIncidenceSet (G G' : SimpleGraph V) (v : V)
    (hG' : G' = G.deleteIncidenceSet v) :
    G.edgeFinset.card = G'.edgeFinset.card + G.degree v := by sorry
