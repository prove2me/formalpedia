-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_coeSet_patch
-- name    : DiscreteTiling.TileSet.coeSet_patch
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:16:55.505797+00:00
-- url     : https://prove2.me/theorems/f4015ab4-db4a-443c-9ecd-33f256ae3f9f
-- title:
--   Tile Set: coe Set patch
-- statement:
--   The Tile Set construction uses the coe Set patch property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Patch.lean#L172-L174
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Patch.lean#L172-L174

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Disjoint
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_TileSetCard
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Patch
set_option autoImplicit false
@[expose] public section
public section
noncomputable section
open DiscreteTiling
open Function
open scoped Cardinal Pointwise
variable {G X ιₚ ιₜ ιₜ' Eᵤ : Type*} [Group G] [MulAction G X] {ps : Protoset G X ιₚ}
universe u
variable {ιᵤ ιᵤ' : Type u} [EquivLike Eᵤ ιᵤ' ιᵤ]
open DiscreteTiling.TileSet

theorem DiscreteTiling.TileSet.coeSet_patch (t : TileSet ps ιₜ) (s : Set X) :
    t.patch s = t '' {i | (s ∩ t i).Nonempty} := by sorry
