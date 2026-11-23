-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_Disjoint_finiteIntersections
-- name    : DiscreteTiling.TileSet.Disjoint.finiteIntersections
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T05:57:26.585316+00:00
-- url     : https://prove2.me/theorems/5098138d-613d-470e-9f4e-4e05756c837b
-- title:
--   Disjoint: finite Intersections
-- statement:
--   The Disjoint construction uses the finite Intersections property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Disjoint.lean#L182-L184
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Disjoint.lean#L182-L184

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

theorem DiscreteTiling.TileSet.Disjoint.finiteIntersections {t : TileSet ps ιₜ} (h : t.Disjoint) :
    t.FiniteIntersections := by sorry
