-- Prove2me | Theorems.Thm_Combinatorics_Line_exists_mono_of_shelahBound_le
-- name    : Combinatorics.Line.exists_mono_of_shelahBound_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:50:40.308302+00:00
-- url     : https://prove2.me/theorems/5e0521cd-50a4-48df-89db-a833becdeaba
-- title:
--   Line: exists mono of shelah Bound le
-- statement:
--   The **Hales--Jewett theorem** with Shelah's bound: over a nonempty alphabet `α`, every coloring
--   of the words indexed by a type of cardinality at least `shelahBound (card α) (card κ)` has a
--   monochromatic line.
--
--   Source: https://github.com/gdahia/ShelahHalesJewett/blob/8a91fc0e8a9617f8ade16ccb3b56e543990c9f45/ShelahHalesJewett/HalesJewett.lean#L190-L203
-- source:
--   https://github.com/gdahia/ShelahHalesJewett/blob/8a91fc0e8a9617f8ade16ccb3b56e543990c9f45/ShelahHalesJewett/HalesJewett.lean#L190-L203

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

theorem Combinatorics.Line.exists_mono_of_shelahBound_le [Nonempty α]
    (h : shelahBound (Fintype.card α) (Fintype.card κ) ≤ Fintype.card ι) (C : (ι → α) → κ) :
    ∃ l : Line α ι, l.IsMono C := by sorry
