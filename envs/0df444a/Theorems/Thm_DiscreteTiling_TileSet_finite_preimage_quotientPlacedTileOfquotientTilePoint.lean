-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_finite_preimage_quotientPlacedTileOfquotientTilePoint
-- name    : DiscreteTiling.TileSet.finite_preimage_quotientPlacedTileOfquotientTilePoint
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T06:05:56.202089+00:00
-- url     : https://prove2.me/theorems/33800236-02e3-4b1f-b787-fb4b0bc7a606
-- title:
--   Tile Set: finite preimage quotient Placed Tile Ofquotient Tile Point
-- statement:
--   The Tile Set construction uses the finite preimage quotient Placed Tile Ofquotient Tile Point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Isohedral.lean#L327-L332
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Isohedral.lean#L327-L332

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

theorem DiscreteTiling.TileSet.finite_preimage_quotientPlacedTileOfquotientTilePoint {t : TileSet ps ιₜ}
    {pt : (t : Set (PlacedTile ps))} (h : ((pt : PlacedTile ps) : Set X).Finite) :
    (t.quotientPlacedTileOfquotientTilePoint ⁻¹' {⟦pt⟧}).Finite := by sorry
