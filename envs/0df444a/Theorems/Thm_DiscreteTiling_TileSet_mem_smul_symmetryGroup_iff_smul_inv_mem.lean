-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_mem_smul_symmetryGroup_iff_smul_inv_mem
-- name    : DiscreteTiling.TileSet.mem_smul_symmetryGroup_iff_smul_inv_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:05:03.665538+00:00
-- url     : https://prove2.me/theorems/66981924-b0f3-4ac8-9272-e3e59ffaadc7
-- title:
--   Tile Set: mem smul symmetry Group iff smul inv mem
-- statement:
--   The Tile Set construction uses the mem smul symmetry Group iff smul inv mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Isohedral.lean#L82-L87
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Isohedral.lean#L82-L87

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

theorem DiscreteTiling.TileSet.mem_smul_symmetryGroup_iff_smul_inv_mem {t : TileSet ps ιₜ} (g : t.symmetryGroup)
    {pt : (t : Set (PlacedTile ps))} {x : X} :
    x ∈ ((g • pt : (t : Set (PlacedTile ps))) : PlacedTile ps) ↔
      g⁻¹ • x ∈ (pt : PlacedTile ps) := by sorry
