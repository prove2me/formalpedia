-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_FiniteIntersections_finiteIntersectionsOn
-- name    : DiscreteTiling.TileSet.FiniteIntersections.finiteIntersectionsOn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T05:59:29.166794+00:00
-- url     : https://prove2.me/theorems/1c4f2fe1-7471-42aa-9f62-94f66484df85
-- title:
--   Finite Intersections: finite Intersections On
-- statement:
--   The Finite Intersections construction uses the finite Intersections On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Disjoint.lean#L250-L252
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Disjoint.lean#L250-L252

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

theorem DiscreteTiling.TileSet.FiniteIntersections.finiteIntersectionsOn (s : Set X) {t : TileSet ps ιₜ}
    (hfi : t.FiniteIntersections) : t.FiniteIntersectionsOn s := by sorry
