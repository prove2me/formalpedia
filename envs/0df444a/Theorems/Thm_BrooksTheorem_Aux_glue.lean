-- Prove2me | Theorems.Thm_BrooksTheorem_Aux_glue
-- name    : BrooksTheorem.Aux.glue
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:31:51.641483+00:00
-- url     : https://prove2.me/theorems/4e00a0e0-3675-5bd9-b14e-a027a63ed049
-- title:
--   Aux: glue
-- statement:
--   Gluing colourings of two sides of a separation.
--
--   Source: https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/BrooksLib/BrooksCore.lean#L65-L83
-- source:
--   https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/BrooksLib/BrooksCore.lean#L65-L83

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

theorem BrooksTheorem.Aux.glue {k : ℕ} (H : SimpleGraph V) (S1 S2 : Set V)
    (hedge : ∀ u v, H.Adj u v → (u ∈ S1 ∧ v ∈ S1) ∨ (u ∈ S2 ∧ v ∈ S2))
    (c1 c2 : V → Fin k) (h1 : Proper (restr H S1) c1) (h2 : Proper (restr H S2) c2)
    (hagree : ∀ v ∈ S1, v ∈ S2 → c1 v = c2 v) : ∃ g : V → Fin k, Proper H g := by sorry
