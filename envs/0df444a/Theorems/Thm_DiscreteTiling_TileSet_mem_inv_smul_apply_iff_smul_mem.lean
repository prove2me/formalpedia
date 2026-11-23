-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_mem_inv_smul_apply_iff_smul_mem
-- name    : DiscreteTiling.TileSet.mem_inv_smul_apply_iff_smul_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T05:53:16.051266+00:00
-- url     : https://prove2.me/theorems/9981693c-387c-4181-ba87-162f4fa39bf1
-- title:
--   Tile Set: mem inv smul apply iff smul mem
-- statement:
--   The Tile Set construction uses the mem inv smul apply iff smul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/TileSet.lean#L267-L269
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/TileSet.lean#L267-L269

module
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Combinatorics.Tiling.Tile
public import Mathlib.GroupTheory.GroupAction.Basic
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_TileSet
set_option autoImplicit false
@[expose] public section
public section
noncomputable section
open DiscreteTiling
open Function
open scoped Pointwise
variable {G X ιₚ : Type*} [Group G] [MulAction G X]
variable {ps : Protoset G X ιₚ} {ι ιₜ ιₜ' ιₜ'' ιₜ''' E E' F : Type*} {ιₜι ιₜ'ι : ι → Type*}
variable [EquivLike E ιₜ' ιₜ] [EquivLike E' ιₜ'' ιₜ'] [FunLike F ιₜ' ιₜ] [EmbeddingLike F ιₜ' ιₜ]
open DiscreteTiling.TileSet
attribute [coe] tiles

theorem DiscreteTiling.TileSet.mem_inv_smul_apply_iff_smul_mem {g : G} {x : X} {t : TileSet ps ιₜ} {i : ιₜ} :
    x ∈ (g⁻¹ • t) i ↔ g • x ∈ t i := by sorry
