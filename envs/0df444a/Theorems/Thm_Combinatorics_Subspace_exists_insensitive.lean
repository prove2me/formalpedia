-- Prove2me | Theorems.Thm_Combinatorics_Subspace_exists_insensitive
-- name    : Combinatorics.Subspace.exists_insensitive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:50:40.950835+00:00
-- url     : https://prove2.me/theorems/2214cc63-cefa-4e14-872a-68a83ca4e3d5
-- title:
--   Subspace: exists insensitive
-- statement:
--   In a cube of dimension `insensitiveBound`, every coloring is insensitive to the letters `a`
--   and `b` on some `η`-dimensional subspace: replacing `a` by `b` in any coordinates of a point of
--   the subspace does not change its color.
--
--   Source: https://github.com/gdahia/ShelahHalesJewett/blob/8a91fc0e8a9617f8ade16ccb3b56e543990c9f45/ShelahHalesJewett/HalesJewett.lean#L65-L104
-- source:
--   https://github.com/gdahia/ShelahHalesJewett/blob/8a91fc0e8a9617f8ade16ccb3b56e543990c9f45/ShelahHalesJewett/HalesJewett.lean#L65-L104

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
open Combinatorics.Subspace

theorem Combinatorics.Subspace.exists_insensitive (α : Type) [Finite α] (a b : α) (η : Type) [Finite η]
    (κ : Type) [Finite κ] :
    ∃ (ι : Type) (_ : Fintype ι),
      Fintype.card ι = insensitiveBound (Nat.card α) (Nat.card η) (Nat.card κ) ∧
      ∀ C : (ι → α) → κ, ∃ V : Subspace η α ι,
        ∀ x y : η → α, (∀ e, x e = y e ∨ x e = a ∧ y e = b) → C (V x) = C (V y) := by sorry
