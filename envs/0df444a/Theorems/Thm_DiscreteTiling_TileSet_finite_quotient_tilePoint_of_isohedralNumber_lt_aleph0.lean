-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_finite_quotient_tilePoint_of_isohedralNumber_lt_aleph0
-- name    : DiscreteTiling.TileSet.finite_quotient_tilePoint_of_isohedralNumber_lt_aleph0
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:07:06.443343+00:00
-- url     : https://prove2.me/theorems/1c42fb6b-2ded-4e1d-aabe-a121a90d0e42
-- title:
--   Tile Set: finite quotient tile Point of isohedral Number lt aleph0
-- statement:
--   The Tile Set construction uses the finite quotient tile Point of isohedral Number lt aleph0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Isohedral.lean#L342-L355
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Isohedral.lean#L342-L355

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

theorem DiscreteTiling.TileSet.finite_quotient_tilePoint_of_isohedralNumber_lt_aleph0 {t : TileSet ps ιₜ}
    (h : t.isohedralNumber < ℵ₀) (hf : ∀ i, (t i : Set X).Finite) :
    Finite (MulAction.orbitRel.Quotient t.symmetryGroup
      {x : Prod (t : Set (PlacedTile ps)) X // x.2 ∈ (x.1 : PlacedTile ps)}) := by sorry
