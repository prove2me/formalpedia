-- Prove2me | Theorems.Thm_BrooksTheorem_Aux_deg_restr
-- name    : BrooksTheorem.Aux.deg_restr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:32:33.036395+00:00
-- url     : https://prove2.me/theorems/0608b548-b236-4fe1-be0f-4c2b391cd038
-- title:
--   Aux: deg restr
-- statement:
--   The Aux construction uses the deg restr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/BrooksLib/BrooksCore.lean#L157-L159
-- source:
--   https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/BrooksLib/BrooksCore.lean#L157-L159

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

theorem BrooksTheorem.Aux.deg_restr {H : SimpleGraph V} {k : ℕ} (hdeg : ∀ v, (nb H v).card ≤ k) (S : Set V) :
    ∀ v, (nb (restr H S) v).card ≤ k := by sorry
