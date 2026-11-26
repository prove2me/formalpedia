-- Prove2me | Theorems.Thm_BrooksTheorem_Aux_restr_adj
-- name    : BrooksTheorem.Aux.restr_adj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:31:38.798921+00:00
-- url     : https://prove2.me/theorems/6bf3c10d-0cc1-47ec-ae56-26fdaa4501c2
-- title:
--   Aux: restr adj
-- statement:
--   The Aux construction uses the restr adj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/BrooksLib/BrooksCore.lean#L35-L36
-- source:
--   https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/BrooksLib/BrooksCore.lean#L35-L36

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

theorem BrooksTheorem.Aux.restr_adj {H : SimpleGraph V} {S : Set V} {u v : V} :
    (restr H S).Adj u v ↔ H.Adj u v ∧ u ∈ S ∧ v ∈ S := by sorry
