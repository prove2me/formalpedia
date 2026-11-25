-- Prove2me | Theorems.Thm_CliqueMinors_exists_adj_of_card_pos
-- name    : CliqueMinors.exists_adj_of_card_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:33:15.157071+00:00
-- url     : https://prove2.me/theorems/2d624793-abb4-4d7e-a7d5-d76448eb9566
-- title:
--   Clique Minors: exists adj of card pos
-- statement:
--   The Clique Minors construction uses the exists adj of card pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/CliqueMinorsLib/GraphOps.lean#L60-L64
-- source:
--   https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/CliqueMinorsLib/GraphOps.lean#L60-L64

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

theorem CliqueMinors.exists_adj_of_card_pos {G : SimpleGraph V} (h : 0 < G.edgeFinset.card) :
    ∃ a b, G.Adj a b := by sorry
