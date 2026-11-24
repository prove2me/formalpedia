-- Prove2me | Theorems.Thm_Combinatorics_Line_exists_mono_of_ack_le
-- name    : Combinatorics.Line.exists_mono_of_ack_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:50:58.128059+00:00
-- url     : https://prove2.me/theorems/a68ca3b7-23f5-42d4-b44f-13a754270699
-- title:
--   Line: exists mono of ack le
-- statement:
--   The **Hales--Jewett theorem** with the Ackermann function as the bound: over a nonempty
--   alphabet `α`, every coloring of the words indexed by `ι` has a monochromatic line if `card ι` is
--   at least `ack 5 (2 * card α + card κ)`.
--
--   Source: https://github.com/gdahia/ShelahHalesJewett/blob/8a91fc0e8a9617f8ade16ccb3b56e543990c9f45/ShelahHalesJewett/Ackermann.lean#L98-L101
-- source:
--   https://github.com/gdahia/ShelahHalesJewett/blob/8a91fc0e8a9617f8ade16ccb3b56e543990c9f45/ShelahHalesJewett/Ackermann.lean#L98-L101

module
public import Mathlib.Computability.Ackermann
public import Definitions.Def_ShelahHalesJewett_HalesJewett
public import Definitions.Def_ShelahHalesJewett_Ackermann
set_option autoImplicit true
@[expose] public section
public section
open Combinatorics
open Combinatorics.Line
variable {α κ ι : Type*} [Fintype α] [Fintype κ] [Fintype ι]

theorem Combinatorics.Line.exists_mono_of_ack_le [Nonempty α]
    (h : ack 5 (2 * Fintype.card α + Fintype.card κ) ≤ Fintype.card ι) (C : (ι → α) → κ) :
    ∃ l : Line α ι, l.IsMono C := by sorry
