-- Prove2me | Theorems.Thm_BrooksTheorem_Aux_deg_addE
-- name    : BrooksTheorem.Aux.deg_addE
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:32:55.506931+00:00
-- url     : https://prove2.me/theorems/77beeb48-d63e-4c3a-97d6-547980b7c80c
-- title:
--   Aux: deg add E
-- statement:
--   The Aux construction uses the deg add E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/BrooksLib/BrooksCore.lean#L173-L195
-- source:
--   https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/BrooksLib/BrooksCore.lean#L173-L195

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

theorem BrooksTheorem.Aux.deg_addE {H : SimpleGraph V} {k : ℕ} (hdeg : ∀ v, (nb H v).card ≤ k) (S : Set V)
    {x z px pz : V} (hpx : H.Adj x px) (hpxS : px ∉ S) (hpz : H.Adj z pz) (hpzS : pz ∉ S) :
    ∀ v, (nb (restr H S ⊔ edge x z) v).card ≤ k := by sorry
