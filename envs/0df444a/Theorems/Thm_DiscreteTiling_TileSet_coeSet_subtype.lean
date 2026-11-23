-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_coeSet_subtype
-- name    : DiscreteTiling.TileSet.coeSet_subtype
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:13:30.958051+00:00
-- url     : https://prove2.me/theorems/aad8b7a1-4e1c-4d36-bc22-79e8e663441b
-- title:
--   Tile Set: coe Set subtype
-- statement:
--   The Tile Set construction uses the coe Set subtype property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Patch.lean#L72-L73
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Patch.lean#L72-L73

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

theorem DiscreteTiling.TileSet.coeSet_subtype (t : TileSet ps ιₜ) (p : ιₜ → Prop) : t.subtype p = t '' {i | p i} := by sorry
