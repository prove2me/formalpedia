-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_finiteIntersectionsOn_iff
-- name    : DiscreteTiling.TileSet.finiteIntersectionsOn_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:01:38.534825+00:00
-- url     : https://prove2.me/theorems/64cdb34d-385c-4c15-b354-c1e45720f405
-- title:
--   Tile Set: finite Intersections On iff
-- statement:
--   The Tile Set construction uses the finite Intersections On iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Disjoint.lean#L203-L205
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Disjoint.lean#L203-L205

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

theorem DiscreteTiling.TileSet.finiteIntersectionsOn_iff {s : Set X} {t : TileSet ps ιₜ} :
    t.FiniteIntersectionsOn s ↔ ∀ x ∈ s, {i | x ∈ t i}.Finite := by sorry
