-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_smul_mem_smul_symmetryGroup_iff
-- name    : DiscreteTiling.TileSet.smul_mem_smul_symmetryGroup_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:09:55.084975+00:00
-- url     : https://prove2.me/theorems/a15efc4d-2c4e-472f-af66-9ecf8bfcd6c7
-- title:
--   Tile Set: smul mem smul symmetry Group iff
-- statement:
--   The Tile Set construction uses the smul mem smul symmetry Group iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Isohedral.lean#L76-L80
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Isohedral.lean#L76-L80

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

theorem DiscreteTiling.TileSet.smul_mem_smul_symmetryGroup_iff {t : TileSet ps ιₜ} (g : t.symmetryGroup)
    {pt : (t : Set (PlacedTile ps))} {x : X} :
    g • x ∈ ((g • pt : (t : Set (PlacedTile ps))) : PlacedTile ps) ↔
      x ∈ (pt : PlacedTile ps) := by sorry
