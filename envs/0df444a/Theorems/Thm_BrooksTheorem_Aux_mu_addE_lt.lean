-- Prove2me | Theorems.Thm_BrooksTheorem_Aux_mu_addE_lt
-- name    : BrooksTheorem.Aux.mu_addE_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:32:25.15281+00:00
-- url     : https://prove2.me/theorems/dfe958ee-de06-4946-851a-f55a0acfbee5
-- title:
--   Aux: mu add E lt
-- statement:
--   The Aux construction uses the mu add E lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/BrooksLib/BrooksCore.lean#L105-L152
-- source:
--   https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/BrooksLib/BrooksCore.lean#L105-L152

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

theorem BrooksTheorem.Aux.mu_addE_lt (H : SimpleGraph V) (S : Set V) {x z px pz : V} (hxz : x ≠ z) (hzS : z ∈ S)
    (hpx : H.Adj x px) (hpxS : px ∉ S) (hpz : H.Adj z pz) (hpzS : pz ∉ S) :
    mu (restr H S ⊔ edge x z) < mu H := by sorry
