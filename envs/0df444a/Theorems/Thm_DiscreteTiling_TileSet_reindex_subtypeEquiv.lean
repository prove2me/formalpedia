-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_reindex_subtypeEquiv
-- name    : DiscreteTiling.TileSet.reindex_subtypeEquiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:14:34.135332+00:00
-- url     : https://prove2.me/theorems/3bbcac12-492d-4109-915d-0b84abad73b1
-- title:
--   Tile Set: reindex subtype Equiv
-- statement:
--   The Tile Set construction uses the reindex subtype Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Patch.lean#L63-L66
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Patch.lean#L63-L66

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Disjoint
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_TileSetCard
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Patch
set_option autoImplicit false
@[expose] public section
public section
noncomputable section
open DiscreteTiling
open Function
open scoped Cardinal Pointwise
variable {G X ιₚ ιₜ ιₜ' Eᵤ : Type*} [Group G] [MulAction G X] {ps : Protoset G X ιₚ}
universe u
variable {ιᵤ ιᵤ' : Type u} [EquivLike Eᵤ ιᵤ' ιᵤ]
open DiscreteTiling.TileSet

theorem DiscreteTiling.TileSet.reindex_subtypeEquiv (t : TileSet ps ιₜ) {p : ιₜ → Prop} {e : ιₜ' ≃ ιₜ} {q : ιₜ' → Prop}
    (h : ∀ i, q i ↔ p (e i)) :
    (t.subtype p).reindex (Equiv.subtypeEquiv e h) = (t.reindex e).subtype q := by sorry
