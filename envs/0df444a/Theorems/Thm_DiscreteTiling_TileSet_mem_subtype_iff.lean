-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_mem_subtype_iff
-- name    : DiscreteTiling.TileSet.mem_subtype_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:13:58.721519+00:00
-- url     : https://prove2.me/theorems/b9c78498-751a-4cc1-a110-2ce7f134e43a
-- title:
--   Tile Set: mem subtype iff
-- statement:
--   The Tile Set construction uses the mem subtype iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Patch.lean#L79-L82
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Patch.lean#L79-L82

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

theorem DiscreteTiling.TileSet.mem_subtype_iff {t : TileSet ps ιₜ} {p : ιₜ → Prop} {pt : PlacedTile ps} :
    pt ∈ t.subtype p ↔ ∃ i, p i ∧ t i = pt := by sorry
