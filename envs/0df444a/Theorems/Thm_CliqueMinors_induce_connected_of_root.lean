-- Prove2me | Theorems.Thm_CliqueMinors_induce_connected_of_root
-- name    : CliqueMinors.induce_connected_of_root
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:38:37.964448+00:00
-- url     : https://prove2.me/theorems/9e831455-4cc6-4e4b-aae7-e9d9910b02e9
-- title:
--   Clique Minors: induce connected of root
-- statement:
--   The Clique Minors construction uses the induce connected of root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/CliqueMinorsLib/Minors.lean#L61-L73
-- source:
--   https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/CliqueMinorsLib/Minors.lean#L61-L73

module
public import Mathlib
public import Definitions.Def_CliqueMinorsLib_GraphOps
public import Definitions.Def_CliqueMinorsLib_Minors
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open CliqueMinors
variable {V W : Type*}
open Relation

theorem CliqueMinors.induce_connected_of_root (G : SimpleGraph V) (B : Finset V) (r : V) (hr : r ∈ B)
    (h : ∀ v ∈ B, ReflTransGen (InAdj G B) r v) : (G.induce (B : Set V)).Connected := by sorry
