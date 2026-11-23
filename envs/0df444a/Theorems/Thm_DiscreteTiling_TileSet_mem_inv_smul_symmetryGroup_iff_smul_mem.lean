-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_mem_inv_smul_symmetryGroup_iff_smul_mem
-- name    : DiscreteTiling.TileSet.mem_inv_smul_symmetryGroup_iff_smul_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:05:21.087551+00:00
-- url     : https://prove2.me/theorems/2492dae2-8e4b-4812-97d9-8c9a25eeca23
-- title:
--   Tile Set: mem inv smul symmetry Group iff smul mem
-- statement:
--   The Tile Set construction uses the mem inv smul symmetry Group iff smul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Isohedral.lean#L89-L94
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Isohedral.lean#L89-L94

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

theorem DiscreteTiling.TileSet.mem_inv_smul_symmetryGroup_iff_smul_mem {t : TileSet ps ιₜ} (g : t.symmetryGroup)
    {pt : (t : Set (PlacedTile ps))} {x : X} :
    x ∈ ((g⁻¹ • pt : (t : Set (PlacedTile ps))) : PlacedTile ps) ↔
      g • x ∈ (pt : PlacedTile ps) := by sorry
