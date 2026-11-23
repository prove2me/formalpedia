-- Prove2me | Theorems.Thm_DiscreteTiling_TileSetFunction_toVarTileSetFunction_ofLE
-- name    : DiscreteTiling.TileSetFunction.toVarTileSetFunction_ofLE
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:01:04.115365+00:00
-- url     : https://prove2.me/theorems/10e2e437-fa7c-4fcc-867a-deb6f6b9070f
-- title:
--   Tile Set Function: to Var Tile Set Function of LE
-- statement:
--   The Tile Set Function construction uses the to Var Tile Set Function of LE property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Basic.lean#L357-L359
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Basic.lean#L357-L359

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

theorem DiscreteTiling.TileSetFunction.toVarTileSetFunction_ofLE (f : TileSetFunction ps α H) {H' : Subgroup G} (h : H' ≤ H) :
    (f.ofLE h).toVarTileSetFunction Y = (f.toVarTileSetFunction Y).ofLE h := by sorry
