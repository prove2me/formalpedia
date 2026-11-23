-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_surjective_quotientPointOfquotientTilePoint
-- name    : DiscreteTiling.TileSet.surjective_quotientPointOfquotientTilePoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:05:46.524023+00:00
-- url     : https://prove2.me/theorems/c8b816dc-b8fc-4efe-838d-488ef1055782
-- title:
--   Tile Set: surjective quotient Point Ofquotient Tile Point
-- statement:
--   The Tile Set construction uses the surjective quotient Point Ofquotient Tile Point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Isohedral.lean#L279-L285
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Isohedral.lean#L279-L285

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Disjoint
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Union
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.SetTheory.Cardinal.Finite
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Isohedral
set_option autoImplicit false
@[expose] public section
public section
noncomputable section
open DiscreteTiling
open Function
open scoped Cardinal Pointwise
variable {G X ιₚ ιₜ : Type*} [Group G] [MulAction G X] {ps : Protoset G X ιₚ}
open DiscreteTiling.TileSet

theorem DiscreteTiling.TileSet.surjective_quotientPointOfquotientTilePoint {t : TileSet ps ιₜ} (h : t.UnionEqUniv) :
    Surjective t.quotientPointOfquotientTilePoint := by sorry
