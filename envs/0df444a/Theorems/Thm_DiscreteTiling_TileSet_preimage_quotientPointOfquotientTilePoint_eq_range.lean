-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_preimage_quotientPointOfquotientTilePoint_eq_range
-- name    : DiscreteTiling.TileSet.preimage_quotientPointOfquotientTilePoint_eq_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:05:49.987949+00:00
-- url     : https://prove2.me/theorems/12877311-81d1-48fd-b14c-3ceba46ed471
-- title:
--   Tile Set: preimage quotient Point Ofquotient Tile Point eq range
-- statement:
--   The Tile Set construction uses the preimage quotient Point Ofquotient Tile Point eq range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Isohedral.lean#L306-L325
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Isohedral.lean#L306-L325

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

theorem DiscreteTiling.TileSet.preimage_quotientPointOfquotientTilePoint_eq_range {t : TileSet ps ιₜ} (x : X) :
    t.quotientPointOfquotientTilePoint ⁻¹' {⟦x⟧} =
      Set.range (fun pt : {pt // pt ∈ t ∧ x ∈ pt} ↦
        ⟦⟨(⟨pt, pt.property.1⟩, x), pt.property.2⟩⟧) := by sorry
