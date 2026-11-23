-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_DisjointOn_finiteIntersectionsOn
-- name    : DiscreteTiling.TileSet.DisjointOn.finiteIntersectionsOn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T05:58:59.701696+00:00
-- url     : https://prove2.me/theorems/73208967-0cb6-46d6-ae68-b1140282e040
-- title:
--   Disjoint On: finite Intersections On
-- statement:
--   The Disjoint On construction uses the finite Intersections On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Disjoint.lean#L239-L248
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Disjoint.lean#L239-L248

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
set_option backward.isDefEq.respectTransparency false

theorem DiscreteTiling.TileSet.DisjointOn.finiteIntersectionsOn {s : Set X} {t : TileSet ps ιₜ}
    (h : t.DisjointOn s) : t.FiniteIntersectionsOn s := by sorry
