-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_Disjoint_coeSet_disjoint
-- name    : DiscreteTiling.TileSet.Disjoint.coeSet_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T05:58:18.886396+00:00
-- url     : https://prove2.me/theorems/fdb98078-c2d3-4114-b889-1b2e62c30d6e
-- title:
--   Disjoint: coe Set disjoint
-- statement:
--   The Disjoint construction uses the coe Set disjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Disjoint.lean#L86-L88
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Disjoint.lean#L86-L88

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

theorem DiscreteTiling.TileSet.Disjoint.coeSet_disjoint {t : TileSet ps ιₜ} (hd : t.Disjoint) :
    (t : Set (PlacedTile ps)).Pairwise fun x y ↦ Disjoint (x : Set X) y := by sorry
