-- Prove2me | Theorems.Thm_DiscreteTiling_TileSetFunction_toVarTileSetFunction_comp
-- name    : DiscreteTiling.TileSetFunction.toVarTileSetFunction_comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:00:59.241237+00:00
-- url     : https://prove2.me/theorems/b283d402-61bd-4fd9-8177-906580c96539
-- title:
--   Tile Set Function: to Var Tile Set Function comp
-- statement:
--   The Tile Set Function construction uses the to Var Tile Set Function comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Basic.lean#L346-L348
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Basic.lean#L346-L348

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_TileSet
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Basic
set_option autoImplicit false
@[expose] public section
public section
noncomputable section
open DiscreteTiling
open Function
open scoped Pointwise
variable {G X Y ιₚ : Type*} [Group G] [MulAction G X] [MulAction G Y]
universe u
variable {ps : Protoset G X ιₚ} {ιᵤ ιᵤ' : Type u} {ιₜ ιₜ' Eᵤ α β γ : Type*}
variable {H : Subgroup G}
variable [EquivLike Eᵤ ιᵤ' ιᵤ]
open DiscreteTiling.TileSetFunction
variable (Y)

theorem DiscreteTiling.TileSetFunction.toVarTileSetFunction_comp (f : TileSetFunction ps α H) (fab : α → β) :
    (f.comp fab).toVarTileSetFunction Y = (f.toVarTileSetFunction Y).comp fab := by sorry
