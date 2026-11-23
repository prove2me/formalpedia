-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_IsTiling_disjoint
-- name    : DiscreteTiling.TileSet.IsTiling.disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T05:58:06.092868+00:00
-- url     : https://prove2.me/theorems/07de5aff-5385-41d4-8c67-3c4ab853752a
-- title:
--   Is Tiling: disjoint
-- statement:
--   The Is Tiling construction uses the disjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Tiling.lean#L99-L100
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Tiling.lean#L99-L100

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Disjoint
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Union
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Tiling
set_option autoImplicit false
@[expose] public section
public section
noncomputable section
open DiscreteTiling
open Function
open scoped Pointwise
variable {G X ιₚ : Type*} [Group G] [MulAction G X]
variable {ps : Protoset G X ιₚ} {ιₜ : Type*}
open DiscreteTiling.TileSet

theorem DiscreteTiling.TileSet.IsTiling.disjoint {t : TileSet ps ιₜ} (h : t.IsTiling) : t.Disjoint := by sorry
