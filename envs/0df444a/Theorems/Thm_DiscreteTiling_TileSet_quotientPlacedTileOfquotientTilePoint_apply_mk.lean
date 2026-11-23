-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_quotientPlacedTileOfquotientTilePoint_apply_mk
-- name    : DiscreteTiling.TileSet.quotientPlacedTileOfquotientTilePoint_apply_mk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:04:29.473796+00:00
-- url     : https://prove2.me/theorems/78b85812-f9b1-4d45-87d6-e6bf8cec02bc
-- title:
--   Tile Set: quotient Placed Tile Ofquotient Tile Point apply mk
-- statement:
--   The Tile Set construction uses the quotient Placed Tile Ofquotient Tile Point apply mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Isohedral.lean#L259-L262
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Isohedral.lean#L259-L262

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

theorem DiscreteTiling.TileSet.quotientPlacedTileOfquotientTilePoint_apply_mk {t : TileSet ps ιₜ}
    (x : {x : Prod (t : Set (PlacedTile ps)) X // x.2 ∈ (x.1 : PlacedTile ps)}) :
    t.quotientPlacedTileOfquotientTilePoint ⟦x⟧ = ⟦(Subtype.val x).1⟧ := by sorry

attribute [defeq] DiscreteTiling.TileSet.quotientPlacedTileOfquotientTilePoint_apply_mk
