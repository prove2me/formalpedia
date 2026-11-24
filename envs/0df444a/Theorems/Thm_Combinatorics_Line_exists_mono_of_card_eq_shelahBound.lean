-- Prove2me | Theorems.Thm_Combinatorics_Line_exists_mono_of_card_eq_shelahBound
-- name    : Combinatorics.Line.exists_mono_of_card_eq_shelahBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:50:40.572216+00:00
-- url     : https://prove2.me/theorems/aba44da3-dfe4-4682-97cd-9292eba7890d
-- title:
--   Line: exists mono of card eq shelah Bound
-- statement:
--   The **Hales--Jewett theorem** with Shelah's bound: every coloring of the words over `α` indexed
--   by a type of cardinality `shelahBound (card α) (card κ)` has a monochromatic line.
--
--   Source: https://github.com/gdahia/ShelahHalesJewett/blob/8a91fc0e8a9617f8ade16ccb3b56e543990c9f45/ShelahHalesJewett/HalesJewett.lean#L172-L185
-- source:
--   https://github.com/gdahia/ShelahHalesJewett/blob/8a91fc0e8a9617f8ade16ccb3b56e543990c9f45/ShelahHalesJewett/HalesJewett.lean#L172-L185

module
public import Mathlib.Combinatorics.HalesJewett
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.SetTheory.Cardinal.NatCard
public import Definitions.Def_ShelahHalesJewett_Line
public import Definitions.Def_ShelahHalesJewett_HalesJewett
set_option autoImplicit true
@[expose] public section
public section
open Combinatorics
open Combinatorics.Line
variable {α κ ι : Type*} [Fintype α] [Fintype κ] [Fintype ι]

theorem Combinatorics.Line.exists_mono_of_card_eq_shelahBound
    (h : Fintype.card ι = shelahBound (Fintype.card α) (Fintype.card κ)) (C : (ι → α) → κ) :
    ∃ l : Line α ι, l.IsMono C := by sorry
