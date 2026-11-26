-- Prove2me | Theorems.Thm_BrooksTheorem_Aux_colour_restr
-- name    : BrooksTheorem.Aux.colour_restr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:31:48.67289+00:00
-- url     : https://prove2.me/theorems/3ed06e57-4283-5a4c-b4c8-edf5eebf9a52
-- title:
--   Aux: colour restr
-- statement:
--   The Aux construction uses the colour restr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/BrooksLib/BrooksCore.lean#L203-L206
-- source:
--   https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/BrooksLib/BrooksCore.lean#L203-L206

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

theorem BrooksTheorem.Aux.colour_restr {k : ℕ} {H : SimpleGraph V} (ih : IHyp k H) (hdeg : ∀ v, (nb H v).card ≤ k)
    (hcf : H.CliqueFree (k + 1)) (S : Set V) {u v : V} (h : H.Adj u v) (hu : u ∉ S) :
    ∃ f : V → Fin k, Proper (restr H S) f := by sorry
