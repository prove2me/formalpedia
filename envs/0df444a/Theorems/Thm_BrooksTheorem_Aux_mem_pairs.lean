-- Prove2me | Theorems.Thm_BrooksTheorem_Aux_mem_pairs
-- name    : BrooksTheorem.Aux.mem_pairs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:31:55.476016+00:00
-- url     : https://prove2.me/theorems/7455a29d-682a-5e19-a3fa-c066c828a60a
-- title:
--   Aux: mem pairs
-- statement:
--   The Aux construction uses the mem pairs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/BrooksLib/BrooksCore.lean#L95-L96
-- source:
--   https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/BrooksLib/BrooksCore.lean#L95-L96

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

theorem BrooksTheorem.Aux.mem_pairs {H : SimpleGraph V} {p : V × V} : p ∈ pairs H ↔ H.Adj p.1 p.2 := by sorry
