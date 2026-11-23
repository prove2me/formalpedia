-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_mem_patch_iff
-- name    : DiscreteTiling.TileSet.mem_patch_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:16:59.440433+00:00
-- url     : https://prove2.me/theorems/24822153-3e9f-45ac-abb3-2385e201f0b2
-- title:
--   Tile Set: mem patch iff
-- statement:
--   The Tile Set construction uses the mem patch iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Patch.lean#L184-L190
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Patch.lean#L184-L190

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

theorem DiscreteTiling.TileSet.mem_patch_iff {t : TileSet ps ιₜ} {s : Set X} {pt : PlacedTile ps} :
    pt ∈ t.patch s ↔ (s ∩ pt).Nonempty ∧ pt ∈ t := by sorry
