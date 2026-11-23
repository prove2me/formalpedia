-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_aleph0_le_isohedralNumber_iff
-- name    : DiscreteTiling.TileSet.aleph0_le_isohedralNumber_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:05:20.28895+00:00
-- url     : https://prove2.me/theorems/41940c3b-3855-4f70-8506-c5dce905e87e
-- title:
--   Tile Set: aleph0 le isohedral Number iff
-- statement:
--   The Tile Set construction uses the aleph0 le isohedral Number iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Isohedral.lean#L182-L185
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Isohedral.lean#L182-L185

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

theorem DiscreteTiling.TileSet.aleph0_le_isohedralNumber_iff {t : TileSet ps ιₜ} :
    ℵ₀ ≤ t.isohedralNumber ↔
      Infinite (MulAction.orbitRel.Quotient t.symmetryGroup (t : Set (PlacedTile ps))) := by sorry
