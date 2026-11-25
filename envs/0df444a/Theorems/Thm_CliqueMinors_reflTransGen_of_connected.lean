-- Prove2me | Theorems.Thm_CliqueMinors_reflTransGen_of_connected
-- name    : CliqueMinors.reflTransGen_of_connected
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:38:40.710611+00:00
-- url     : https://prove2.me/theorems/14bff4e4-bf28-415b-812f-8ff8367db2c4
-- title:
--   Clique Minors: refl Trans Gen of connected
-- statement:
--   The Clique Minors construction uses the refl Trans Gen of connected property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/CliqueMinorsLib/Minors.lean#L75-L79
-- source:
--   https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/CliqueMinorsLib/Minors.lean#L75-L79

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

theorem CliqueMinors.reflTransGen_of_connected {G : SimpleGraph V} {B : Finset V}
    (h : (G.induce (B : Set V)).Connected) {u v : V} (hu : u ∈ B) (hv : v ∈ B) :
    ReflTransGen (InAdj G B) u v := by sorry
