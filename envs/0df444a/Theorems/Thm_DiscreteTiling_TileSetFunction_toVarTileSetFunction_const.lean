-- Prove2me | Theorems.Thm_DiscreteTiling_TileSetFunction_toVarTileSetFunction_const
-- name    : DiscreteTiling.TileSetFunction.toVarTileSetFunction_const
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T05:55:35.988622+00:00
-- url     : https://prove2.me/theorems/c11e3219-997b-4b91-9a12-ec5c5adf0f5d
-- title:
--   Tile Set Function: to Var Tile Set Function const
-- statement:
--   The Tile Set Function construction uses the to Var Tile Set Function const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Basic.lean#L341-L343
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Basic.lean#L341-L343

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
variable (Y ps H)

theorem DiscreteTiling.TileSetFunction.toVarTileSetFunction_const (a : α) :
    (TileSetFunction.const ps H a).toVarTileSetFunction Y = VarTileSetFunction.const Y ps H a := by sorry

attribute [defeq] DiscreteTiling.TileSetFunction.toVarTileSetFunction_const
