-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_smul_subtype
-- name    : DiscreteTiling.TileSet.smul_subtype
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:14:56.394029+00:00
-- url     : https://prove2.me/theorems/767f9547-19ed-4ccc-8ecc-46e76aee797a
-- title:
--   Tile Set: smul subtype
-- statement:
--   The Tile Set construction uses the smul subtype property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Patch.lean#L88-L90
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Patch.lean#L88-L90

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

theorem DiscreteTiling.TileSet.smul_subtype (g : G) (t : TileSet ps ιₜ) (p : ιₜ → Prop) :
    g • (t.subtype p) = (g • t).subtype p := by sorry
