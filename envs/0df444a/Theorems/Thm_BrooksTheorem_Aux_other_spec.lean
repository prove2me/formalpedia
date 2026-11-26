-- Prove2me | Theorems.Thm_BrooksTheorem_Aux_other_spec
-- name    : BrooksTheorem.Aux.other_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:27:35.305086+00:00
-- url     : https://prove2.me/theorems/fd25934c-7e91-5b9a-8f7d-8c207d043bea
-- title:
--   Aux: other spec
-- statement:
--   The Aux construction uses the other spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/BrooksLib/Cycle.lean#L31-L42
-- source:
--   https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/BrooksLib/Cycle.lean#L31-L42

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

theorem BrooksTheorem.Aux.other_spec (G : SimpleGraph V) (h2 : ∀ v, (nb G v).card = 2) (a b : V) :
    G.Adj a (other G a b) ∧ other G a b ≠ b := by sorry
