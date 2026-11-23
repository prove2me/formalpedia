-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_DisjointOn_finiteDistinctIntersectionsOn
-- name    : DiscreteTiling.TileSet.DisjointOn.finiteDistinctIntersectionsOn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T05:59:32.400796+00:00
-- url     : https://prove2.me/theorems/ede37300-245f-4bb2-9136-15ebcb423b6e
-- title:
--   Disjoint On: finite Distinct Intersections On
-- statement:
--   The Disjoint On construction uses the finite Distinct Intersections On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Disjoint.lean#L375-L377
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Disjoint.lean#L375-L377

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

theorem DiscreteTiling.TileSet.DisjointOn.finiteDistinctIntersectionsOn {s : Set X} {t : TileSet ps ιₜ}
    (h : t.DisjointOn s) : t.FiniteDistinctIntersectionsOn s := by sorry
