-- Prove2me | Theorems.Thm_BrooksTheorem_Aux_addE_adj
-- name    : BrooksTheorem.Aux.addE_adj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:31:34.49779+00:00
-- url     : https://prove2.me/theorems/8554e95f-b701-5712-b6b7-b05b84a65eba
-- title:
--   Aux: add E adj
-- statement:
--   The Aux construction uses the add E adj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/BrooksLib/BrooksCore.lean#L40-L42
-- source:
--   https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/BrooksLib/BrooksCore.lean#L40-L42

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

theorem BrooksTheorem.Aux.addE_adj {H : SimpleGraph V} {x z u v : V} :
    (H ⊔ edge x z).Adj u v ↔ H.Adj u v ∨ ((u = x ∧ v = z ∨ u = z ∧ v = x) ∧ u ≠ v) := by sorry
