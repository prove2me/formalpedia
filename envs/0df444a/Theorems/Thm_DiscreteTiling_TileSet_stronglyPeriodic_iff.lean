-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_stronglyPeriodic_iff
-- name    : DiscreteTiling.TileSet.stronglyPeriodic_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:07:54.150803+00:00
-- url     : https://prove2.me/theorems/a8b89178-73eb-4a42-929a-fa3a43260c8d
-- title:
--   Tile Set: strongly Periodic iff
-- statement:
--   The Tile Set construction uses the strongly Periodic iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Periodic.lean#L87-L89
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Periodic.lean#L87-L89

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

theorem DiscreteTiling.TileSet.stronglyPeriodic_iff {t : TileSet ps ιₜ} :
    t.StronglyPeriodic ↔ Finite (MulAction.orbitRel.Quotient t.symmetryGroup X) := by sorry
