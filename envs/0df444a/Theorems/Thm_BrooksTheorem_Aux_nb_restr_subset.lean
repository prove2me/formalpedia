-- Prove2me | Theorems.Thm_BrooksTheorem_Aux_nb_restr_subset
-- name    : BrooksTheorem.Aux.nb_restr_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:32:33.733557+00:00
-- url     : https://prove2.me/theorems/088295a8-64a8-485e-8280-829529d58f2b
-- title:
--   Aux: nb restr subset
-- statement:
--   The Aux construction uses the nb restr subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/BrooksLib/BrooksCore.lean#L154-L155
-- source:
--   https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/BrooksLib/BrooksCore.lean#L154-L155

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

theorem BrooksTheorem.Aux.nb_restr_subset (H : SimpleGraph V) (S : Set V) (v : V) : nb (restr H S) v ⊆ nb H v := by sorry
