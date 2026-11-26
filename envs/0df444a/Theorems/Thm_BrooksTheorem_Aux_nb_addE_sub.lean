-- Prove2me | Theorems.Thm_BrooksTheorem_Aux_nb_addE_sub
-- name    : BrooksTheorem.Aux.nb_addE_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:33:01.120049+00:00
-- url     : https://prove2.me/theorems/d1368300-e64d-4bd1-b67d-39564af8dc45
-- title:
--   Aux: nb add E sub
-- statement:
--   The Aux construction uses the nb add E sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/BrooksLib/BrooksCore.lean#L161-L171
-- source:
--   https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/BrooksLib/BrooksCore.lean#L161-L171

module
public import Definitions.Def_BrooksLib_Greedy
public import Definitions.Def_BrooksLib_BrooksCore
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BrooksTheorem
open BrooksTheorem.Aux
variable {V : Type*}
variable [Fintype V]

theorem BrooksTheorem.Aux.nb_addE_sub [DecidableEq V] (H : SimpleGraph V) (S : Set V) {x z w w' pw : V}
    (hw : (w = x ∧ w' = z) ∨ (w = z ∧ w' = x)) (hpwS : pw ∉ S) :
    nb (restr H S ⊔ edge x z) w ⊆ insert w' ((nb H w).erase pw) := by sorry
