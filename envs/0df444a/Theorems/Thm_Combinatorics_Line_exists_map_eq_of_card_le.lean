-- Prove2me | Theorems.Thm_Combinatorics_Line_exists_map_eq_of_card_le
-- name    : Combinatorics.Line.exists_map_eq_of_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:50:22.294017+00:00
-- url     : https://prove2.me/theorems/7582237c-b3ee-4204-b118-b26e1fa2463c
-- title:
--   Line: exists map eq of card le
-- statement:
--   If a cube of dimension `N` is colored with at most `N` colors, then for any two letters `a` and
--   `b` some line has the same color at `a` and at `b`.
--
--   The `N + 1` words that are `a` on an initial segment of the coordinates and `b` afterwards cannot
--   have distinct colors. Two of them with the same color are the points at `a` and at `b` of the line
--   whose wildcards are the coordinates on which they differ.
--
--   Source: https://github.com/gdahia/ShelahHalesJewett/blob/8a91fc0e8a9617f8ade16ccb3b56e543990c9f45/ShelahHalesJewett/Line.lean#L54-L66
-- source:
--   https://github.com/gdahia/ShelahHalesJewett/blob/8a91fc0e8a9617f8ade16ccb3b56e543990c9f45/ShelahHalesJewett/Line.lean#L54-L66

module
public import Mathlib.Combinatorics.HalesJewett
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Data.Fintype.Pigeonhole
public import Definitions.Def_ShelahHalesJewett_Line
set_option autoImplicit true
@[expose] public section
public section
open Combinatorics
variable {η α ι ι' κ : Type*}
open Combinatorics.Line

theorem Combinatorics.Line.exists_map_eq_of_card_le [Finite κ] {N : ℕ} (hN : Nat.card κ ≤ N) (a b : α)
    (C : (Fin N → α) → κ) : ∃ l : Line α (Fin N), C (l a) = C (l b) := by sorry
