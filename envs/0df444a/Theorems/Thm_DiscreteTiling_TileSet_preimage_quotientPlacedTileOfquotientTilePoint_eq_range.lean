-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_preimage_quotientPlacedTileOfquotientTilePoint_eq_range
-- name    : DiscreteTiling.TileSet.preimage_quotientPlacedTileOfquotientTilePoint_eq_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:05:55.829791+00:00
-- url     : https://prove2.me/theorems/67f0588e-a27c-4a0a-ab4f-834bcd962416
-- title:
--   Tile Set: preimage quotient Placed Tile Ofquotient Tile Point eq range
-- statement:
--   The Tile Set construction uses the preimage quotient Placed Tile Ofquotient Tile Point eq range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Isohedral.lean#L287-L304
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Isohedral.lean#L287-L304

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

theorem DiscreteTiling.TileSet.preimage_quotientPlacedTileOfquotientTilePoint_eq_range {t : TileSet ps ιₜ}
    (pt : (t : Set (PlacedTile ps))) : t.quotientPlacedTileOfquotientTilePoint ⁻¹' {⟦pt⟧} =
      Set.range (fun x : {x // x ∈ (pt : PlacedTile ps)} ↦ ⟦⟨(pt, x), x.property⟩⟧) := by sorry
