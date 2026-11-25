-- Prove2me | Theorems.Thm_CliqueMinors_induce_connected_mono
-- name    : CliqueMinors.induce_connected_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:38:33.903526+00:00
-- url     : https://prove2.me/theorems/525d493e-c371-57d5-932b-1582732d2247
-- title:
--   Clique Minors: induce connected mono
-- statement:
--   The Clique Minors construction uses the induce connected mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/CliqueMinorsLib/Minors.lean#L81-L86
-- source:
--   https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/CliqueMinorsLib/Minors.lean#L81-L86

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

theorem CliqueMinors.induce_connected_mono {G G' : SimpleGraph V} (hle : G' ≤ G) {B : Finset V}
    (h : (G'.induce (B : Set V)).Connected) : (G.induce (B : Set V)).Connected := by sorry
