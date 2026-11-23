-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_quotientPointOfquotientTilePoint_apply_mk
-- name    : DiscreteTiling.TileSet.quotientPointOfquotientTilePoint_apply_mk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:04:20.131116+00:00
-- url     : https://prove2.me/theorems/74f073f3-ee0c-4be1-a72e-ceaef52a13fb
-- title:
--   Tile Set: quotient Point Ofquotient Tile Point apply mk
-- statement:
--   The Tile Set construction uses the quotient Point Ofquotient Tile Point apply mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Isohedral.lean#L264-L267
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Isohedral.lean#L264-L267

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

theorem DiscreteTiling.TileSet.quotientPointOfquotientTilePoint_apply_mk {t : TileSet ps ιₜ}
    (x : {x : Prod (t : Set (PlacedTile ps)) X // x.2 ∈ (x.1 : PlacedTile ps)}) :
      t.quotientPointOfquotientTilePoint ⟦x⟧ = ⟦(Subtype.val x).2⟧ := by sorry

attribute [defeq] DiscreteTiling.TileSet.quotientPointOfquotientTilePoint_apply_mk
