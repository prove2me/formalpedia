-- Prove2me | Theorems.Thm_DiscreteTiling_Protoset_WeaklyAperiodic_aleph0_le_isohedralNumber
-- name    : DiscreteTiling.Protoset.WeaklyAperiodic.aleph0_le_isohedralNumber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:09:04.652599+00:00
-- url     : https://prove2.me/theorems/6171d85d-69b8-4dfa-9347-080eda4be1eb
-- title:
--   Weakly Aperiodic: aleph0 le isohedral Number
-- statement:
--   The Weakly Aperiodic construction uses the aleph0 le isohedral Number property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Periodic.lean#L357-L366
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Periodic.lean#L357-L366

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Tiling
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Isohedral
public import Mathlib.Algebra.Order.Group.Basic
public import Mathlib.LinearAlgebra.FreeModule.Int
public import Mathlib.GroupTheory.OrderOfElement
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Periodic
set_option autoImplicit false
@[expose] public section
public section
noncomputable section
open DiscreteTiling
open Function
open scoped Cardinal Nat Pointwise
variable {G X ιₚ ιₜ : Type*} [Group G] [MulAction G X] {ps : Protoset G X ιₚ}
open DiscreteTiling.Protoset
variable {H : Subgroup G}

theorem DiscreteTiling.Protoset.WeaklyAperiodic.aleph0_le_isohedralNumber {p : TileSetFunction ps Prop H}
    (h : ps.WeaklyAperiodic ιₜ p) (hf : ∀ i, (ps i : Set X).Finite)
    (hu : ∀ t : TileSet ps ιₜ, p t → t.UnionEqUniv) : ℵ₀ ≤ ps.isohedralNumber ιₜ p := by sorry
