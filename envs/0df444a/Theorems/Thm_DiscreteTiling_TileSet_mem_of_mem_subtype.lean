-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_mem_of_mem_subtype
-- name    : DiscreteTiling.TileSet.mem_of_mem_subtype
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:14:00.037815+00:00
-- url     : https://prove2.me/theorems/1ab1ad04-c911-4168-a22f-7ffdb70870ad
-- title:
--   Tile Set: mem of mem subtype
-- statement:
--   The Tile Set construction uses the mem of mem subtype property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Patch.lean#L84-L86
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Patch.lean#L84-L86

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

theorem DiscreteTiling.TileSet.mem_of_mem_subtype {t : TileSet ps ιₜ} {p : ιₜ → Prop} {pt : PlacedTile ps}
    (h : pt ∈ t.subtype p) : pt ∈ t := by sorry
