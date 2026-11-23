-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_stronglyPeriodic_of_pretransitive_of_index_ne_zero
-- name    : DiscreteTiling.TileSet.stronglyPeriodic_of_pretransitive_of_index_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:11:55.893797+00:00
-- url     : https://prove2.me/theorems/c2e2f21d-e408-40ab-8847-a46e6e64d4c2
-- title:
--   Tile Set: strongly Periodic of pretransitive of index ne zero
-- statement:
--   The Tile Set construction uses the strongly Periodic of pretransitive of index ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Periodic.lean#L96-L99
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Periodic.lean#L96-L99

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

theorem DiscreteTiling.TileSet.stronglyPeriodic_of_pretransitive_of_index_ne_zero {t : TileSet ps ιₜ}
    [MulAction.IsPretransitive G X] (hi : t.symmetryGroup.index ≠ 0) :
    t.StronglyPeriodic := by sorry
