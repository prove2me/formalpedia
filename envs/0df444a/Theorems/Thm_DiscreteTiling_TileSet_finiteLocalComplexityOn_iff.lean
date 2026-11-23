-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_finiteLocalComplexityOn_iff
-- name    : DiscreteTiling.TileSet.finiteLocalComplexityOn_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:13:46.510441+00:00
-- url     : https://prove2.me/theorems/861a7b47-ca64-4981-ac33-5728b3713b40
-- title:
--   Tile Set: finite Local Complexity On iff
-- statement:
--   The Tile Set construction uses the finite Local Complexity On iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/FiniteLocalComplexity.lean#L68-L72
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/FiniteLocalComplexity.lean#L68-L72

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

theorem DiscreteTiling.TileSet.finiteLocalComplexityOn_iff {H : Subgroup G} {s : Set (Set X)} {t : TileSet ps ιₜ} :
    t.FiniteLocalComplexityOn H s ↔
      ((fun x ↦ Quotient.mk (MulAction.orbitRel H (Set X × TileSetCard ps))
        (x, (t.patch x).card)) '' s).Finite := by sorry
