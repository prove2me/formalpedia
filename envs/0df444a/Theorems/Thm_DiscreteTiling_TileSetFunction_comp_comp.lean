-- Prove2me | Theorems.Thm_DiscreteTiling_TileSetFunction_comp_comp
-- name    : DiscreteTiling.TileSetFunction.comp_comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T05:56:57.279495+00:00
-- url     : https://prove2.me/theorems/14bc74e3-eb20-453c-b397-c23db134943f
-- title:
--   Tile Set Function: comp comp
-- statement:
--   The Tile Set Function construction uses the comp comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Basic.lean#L148-L150
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Basic.lean#L148-L150

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_TileSet
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Basic
public import Theorems.Thm_DiscreteTiling_TileSet_coeSet_sigma
public import Theorems.Thm_DiscreteTiling_TileSet_coeSet_sum
public import Theorems.Thm_DiscreteTiling_TileSet_coe_sigma
public import Theorems.Thm_DiscreteTiling_TileSet_coe_sum
public import Theorems.Thm_DiscreteTiling_TileSet_mem_sum
public import Theorems.Thm_DiscreteTiling_TileSet_smul_prod_one
public import Theorems.Thm_DiscreteTiling_TileSet_smul_prod_refl
public import Theorems.Thm_DiscreteTiling_TileSet_symmetryGroup_of_isEmpty
public import Theorems.Thm_DiscreteTiling_TileSet_symmetryGroup_reindex
public import Theorems.Thm_DiscreteTiling_TileSet_symmetryGroup_reindex_of_bijective
attribute [local simp] DiscreteTiling.TileSet.coeSet_sigma
attribute [local simp] DiscreteTiling.TileSet.coeSet_sum
attribute [local simp] DiscreteTiling.TileSet.coe_sigma
attribute [local simp] DiscreteTiling.TileSet.coe_sum
attribute [local simp] DiscreteTiling.TileSet.mem_sum
attribute [local simp] DiscreteTiling.TileSet.smul_prod_one
attribute [local simp] DiscreteTiling.TileSet.smul_prod_refl
attribute [local simp] DiscreteTiling.TileSet.symmetryGroup_of_isEmpty
attribute [local simp] DiscreteTiling.TileSet.symmetryGroup_reindex
attribute [local simp] DiscreteTiling.TileSet.symmetryGroup_reindex_of_bijective


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
attribute [coe] toFun
attribute [simp] smul_eq

theorem DiscreteTiling.TileSetFunction.comp_comp (f : TileSetFunction ps α H) (fab : α → β) (fbg : β → γ) :
    f.comp (fbg ∘ fab) = (f.comp fab).comp fbg := by sorry
