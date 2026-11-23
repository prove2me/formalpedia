-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_coe_smul_tilePoint
-- name    : DiscreteTiling.TileSet.coe_smul_tilePoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:04:59.050607+00:00
-- url     : https://prove2.me/theorems/8b926f6b-eda1-49f1-b771-529f92d96be6
-- title:
--   Tile Set: coe smul tile Point
-- statement:
--   The Tile Set construction uses the coe smul tile Point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Isohedral.lean#L225-L229
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Isohedral.lean#L225-L229

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

theorem DiscreteTiling.TileSet.coe_smul_tilePoint {t : TileSet ps ιₜ} (g : t.symmetryGroup)
    (x : {x : Prod (t : Set (PlacedTile ps)) X // x.2 ∈ (x.1 : PlacedTile ps)}) :
    ((g • x : {x : Prod (t : Set (PlacedTile ps)) X // x.2 ∈ (x.1 : PlacedTile ps)}) : Prod _ _) =
      g • (x : Prod (t : Set (PlacedTile ps)) X) := by sorry
