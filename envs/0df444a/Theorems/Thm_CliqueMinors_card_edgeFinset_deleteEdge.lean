-- Prove2me | Theorems.Thm_CliqueMinors_card_edgeFinset_deleteEdge
-- name    : CliqueMinors.card_edgeFinset_deleteEdge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:41:48.460588+00:00
-- url     : https://prove2.me/theorems/b3545fab-41f5-4ff7-8987-307d3dc2c868
-- title:
--   Clique Minors: card edge Finset delete Edge
-- statement:
--   The Clique Minors construction uses the card edge Finset delete Edge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/CliqueMinorsLib/MaderFive.lean#L65-L74
-- source:
--   https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/CliqueMinorsLib/MaderFive.lean#L65-L74

module
public import Mathlib
public import Definitions.Def_CliqueMinorsLib_Minors
public import Definitions.Def_CliqueMinorsLib_MaderFive
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open CliqueMinors
variable {V : Type*}
open scoped Classical
variable [Fintype V]

theorem CliqueMinors.card_edgeFinset_deleteEdge {G : SimpleGraph V} {e : Sym2 V} (he : e ∈ G.edgeFinset) :
    (G.deleteEdges {e}).edgeFinset.card + 1 = G.edgeFinset.card := by sorry
