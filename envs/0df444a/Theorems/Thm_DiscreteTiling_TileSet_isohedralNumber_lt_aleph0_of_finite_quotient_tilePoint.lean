-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_isohedralNumber_lt_aleph0_of_finite_quotient_tilePoint
-- name    : DiscreteTiling.TileSet.isohedralNumber_lt_aleph0_of_finite_quotient_tilePoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:07:06.670954+00:00
-- url     : https://prove2.me/theorems/40071c4c-e6e3-473e-bd3e-3163bbdffb83
-- title:
--   Tile Set: isohedral Number lt aleph0 of finite quotient tile Point
-- statement:
--   The Tile Set construction uses the isohedral Number lt aleph0 of finite quotient tile Point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Isohedral.lean#L357-L364
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Isohedral.lean#L357-L364

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

theorem DiscreteTiling.TileSet.isohedralNumber_lt_aleph0_of_finite_quotient_tilePoint {t : TileSet ps ιₜ}
    (hf : Finite (MulAction.orbitRel.Quotient t.symmetryGroup
      {x : Prod (t : Set (PlacedTile ps)) X // x.2 ∈ (x.1 : PlacedTile ps)}))
    (hn : ∀ i, (t i : Set X).Nonempty) : t.isohedralNumber < ℵ₀ := by sorry
