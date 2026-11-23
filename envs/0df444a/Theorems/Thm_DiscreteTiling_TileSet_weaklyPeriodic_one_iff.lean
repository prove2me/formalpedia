-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_weaklyPeriodic_one_iff
-- name    : DiscreteTiling.TileSet.weaklyPeriodic_one_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:17:44.164194+00:00
-- url     : https://prove2.me/theorems/b06a5e21-d406-46a2-9b32-27e7aeedd90f
-- title:
--   Tile Set: weakly Periodic one iff
-- statement:
--   The Tile Set construction uses the weakly Periodic one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Periodic.lean#L222-L239
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Periodic.lean#L222-L239

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
open DiscreteTiling.TileSet

theorem DiscreteTiling.TileSet.weaklyPeriodic_one_iff {t : TileSet ps ιₜ} :
    t.WeaklyPeriodic 1 ↔ ∃ g ∈ t.symmetryGroup, ¬IsOfFinOrder g := by sorry
