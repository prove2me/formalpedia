-- Prove2me | Theorems.Thm_BrooksTheorem_Aux_mem_nb
-- name    : BrooksTheorem.Aux.mem_nb
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:25:46.505129+00:00
-- url     : https://prove2.me/theorems/7c11c205-3be3-4679-8c45-d9e75dc92e67
-- title:
--   Aux: mem nb
-- statement:
--   The Aux construction uses the mem nb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/BrooksLib/Greedy.lean#L37-L38
-- source:
--   https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/BrooksLib/Greedy.lean#L37-L38

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

theorem BrooksTheorem.Aux.mem_nb {H : SimpleGraph V} {v u : V} : u ∈ nb H v ↔ H.Adj v u := by sorry
