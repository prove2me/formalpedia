-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_finiteLocalComplexity_iff
-- name    : DiscreteTiling.TileSet.finiteLocalComplexity_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:14:29.299882+00:00
-- url     : https://prove2.me/theorems/dcaa7c3b-20b0-48a5-b793-fa1c367b9a65
-- title:
--   Tile Set: finite Local Complexity iff
-- statement:
--   The Tile Set construction uses the finite Local Complexity iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/FiniteLocalComplexity.lean#L96-L100
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/FiniteLocalComplexity.lean#L96-L100

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

theorem DiscreteTiling.TileSet.finiteLocalComplexity_iff {H : Subgroup G} {t : TileSet ps ιₜ} :
    t.FiniteLocalComplexity H ↔
      ((fun x ↦ Quotient.mk (MulAction.orbitRel H (Set X × TileSetCard ps))
        (x, (t.patch x).card)) '' (Set.range Singleton.singleton)).Finite := by sorry
