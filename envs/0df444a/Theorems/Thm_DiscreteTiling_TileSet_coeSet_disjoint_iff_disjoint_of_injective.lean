-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_coeSet_disjoint_iff_disjoint_of_injective
-- name    : DiscreteTiling.TileSet.coeSet_disjoint_iff_disjoint_of_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T05:57:47.68523+00:00
-- url     : https://prove2.me/theorems/34dc63a5-0fe2-4e23-91ec-6b2c80dd1808
-- title:
--   Tile Set: coe Set disjoint iff disjoint of injective
-- statement:
--   The Tile Set construction uses the coe Set disjoint iff disjoint of injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Disjoint.lean#L90-L92
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Disjoint.lean#L90-L92

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Basic
public import Mathlib.Logic.Equiv.Pairwise
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Disjoint
set_option autoImplicit false
@[expose] public section
public section
noncomputable section
open DiscreteTiling
open Function
open scoped Pointwise
variable {G X ιₚ : Type*} [Group G] [MulAction G X]
variable {ps : Protoset G X ιₚ} {ιₜ ιₜ' F : Type*}
variable [FunLike F ιₜ' ιₜ] [EmbeddingLike F ιₜ' ιₜ]
open DiscreteTiling.TileSet

theorem DiscreteTiling.TileSet.coeSet_disjoint_iff_disjoint_of_injective {t : TileSet ps ιₜ} (h : Injective t) :
    ((t : Set (PlacedTile ps)).Pairwise fun x y ↦ Disjoint (x : Set X) y) ↔ t.Disjoint := by sorry
