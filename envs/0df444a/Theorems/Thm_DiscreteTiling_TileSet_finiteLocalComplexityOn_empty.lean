-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_finiteLocalComplexityOn_empty
-- name    : DiscreteTiling.TileSet.finiteLocalComplexityOn_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:17:22.251797+00:00
-- url     : https://prove2.me/theorems/f2880606-9ecc-46bc-9b9b-10645f6ce1f3
-- title:
--   Tile Set: finite Local Complexity On empty
-- statement:
--   The Tile Set construction uses the finite Local Complexity On empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/FiniteLocalComplexity.lean#L74-L76
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/FiniteLocalComplexity.lean#L74-L76

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Basic
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Patch
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_TileSetCard
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_FiniteLocalComplexity
set_option autoImplicit false
@[expose] public section
public section
noncomputable section
open DiscreteTiling
open Function
open scoped Pointwise
variable {G X ιₚ : Type*} [Group G] [MulAction G X]
variable {ps : Protoset G X ιₚ} {ιₜ ιₜ' : Type*}
open DiscreteTiling.TileSet

theorem DiscreteTiling.TileSet.finiteLocalComplexityOn_empty {H : Subgroup G} {t : TileSet ps ιₜ} :
    t.FiniteLocalComplexityOn H ∅ := by sorry
