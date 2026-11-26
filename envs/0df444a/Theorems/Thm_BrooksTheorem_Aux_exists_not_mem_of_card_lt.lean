-- Prove2me | Theorems.Thm_BrooksTheorem_Aux_exists_not_mem_of_card_lt
-- name    : BrooksTheorem.Aux.exists_not_mem_of_card_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:25:51.309307+00:00
-- url     : https://prove2.me/theorems/229476ed-768c-41b5-ba1f-516a125ff559
-- title:
--   Aux: exists not mem of card lt
-- statement:
--   The Aux construction uses the exists not mem of card lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/BrooksLib/Greedy.lean#L41-L48
-- source:
--   https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/BrooksLib/Greedy.lean#L41-L48

module
public import Mathlib
public import Definitions.Def_BrooksLib_Greedy
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BrooksTheorem
open BrooksTheorem.Aux
variable {V : Type*}
variable [Fintype V]

theorem BrooksTheorem.Aux.exists_not_mem_of_card_lt {k : ℕ} (C : Finset (Fin k)) (h : C.card < k) :
    ∃ c : Fin k, c ∉ C := by sorry
