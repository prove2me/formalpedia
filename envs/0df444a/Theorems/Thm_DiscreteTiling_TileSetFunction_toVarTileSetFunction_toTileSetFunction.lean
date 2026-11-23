-- Prove2me | Theorems.Thm_DiscreteTiling_TileSetFunction_toVarTileSetFunction_toTileSetFunction
-- name    : DiscreteTiling.TileSetFunction.toVarTileSetFunction_toTileSetFunction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T05:55:29.247547+00:00
-- url     : https://prove2.me/theorems/c927ef08-17a3-455e-bd2c-42b7d4fc44b2
-- title:
--   Tile Set Function: to Var Tile Set Function to Tile Set Function
-- statement:
--   The Tile Set Function construction uses the to Var Tile Set Function to Tile Set Function property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Basic.lean#L361-L363
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Basic.lean#L361-L363

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

theorem DiscreteTiling.TileSetFunction.toVarTileSetFunction_toTileSetFunction (f : TileSetFunction ps α H) (y : Y) :
    (f.toVarTileSetFunction Y).toTileSetFunction y = f.ofLE inf_le_left := by sorry

attribute [defeq] DiscreteTiling.TileSetFunction.toVarTileSetFunction_toTileSetFunction
