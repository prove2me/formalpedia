-- Prove2me | Theorems.Thm_BrooksTheorem_Aux_sq_add_two
-- name    : BrooksTheorem.Aux.sq_add_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:27:43.12131+00:00
-- url     : https://prove2.me/theorems/74aee01f-9915-5e29-8f15-16b475efd49c
-- title:
--   Aux: sq add two
-- statement:
--   The Aux construction uses the sq add two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/BrooksLib/Cycle.lean#L55-L56
-- source:
--   https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/BrooksLib/Cycle.lean#L55-L56

module
public import Definitions.Def_BrooksLib_Greedy
public import Definitions.Def_BrooksLib_Cycle
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BrooksTheorem
open BrooksTheorem.Aux
variable {V : Type*} [Fintype V]
variable (G : SimpleGraph V) (h2 : ∀ v, (nb G v).card = 2) (v0 v1 : V) (h01 : G.Adj v0 v1)

theorem BrooksTheorem.Aux.sq_add_two (n : ℕ) :
    sq G v0 v1 (n + 2) = other G (sq G v0 v1 (n + 1)) (sq G v0 v1 n) := by sorry
