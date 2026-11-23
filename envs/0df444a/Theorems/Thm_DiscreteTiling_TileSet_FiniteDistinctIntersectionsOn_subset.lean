-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_FiniteDistinctIntersectionsOn_subset
-- name    : DiscreteTiling.TileSet.FiniteDistinctIntersectionsOn.subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:02:28.761078+00:00
-- url     : https://prove2.me/theorems/5ad340f0-38cc-4380-96c7-22c39f2f633b
-- title:
--   Finite Distinct Intersections On: subset
-- statement:
--   The Finite Distinct Intersections On construction uses the subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Disjoint.lean#L362-L365
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Disjoint.lean#L362-L365

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

theorem DiscreteTiling.TileSet.FiniteDistinctIntersectionsOn.subset {s₁ s₂ : Set X} {t : TileSet ps ιₜ}
    (hfi : t.FiniteDistinctIntersectionsOn s₂) (hs : s₁ ⊆ s₂) :
    t.FiniteDistinctIntersectionsOn s₁ := by sorry
