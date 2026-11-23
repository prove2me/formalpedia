-- Prove2me | Theorems.Thm_DiscreteTiling_TileSet_smul_prod_one
-- name    : DiscreteTiling.TileSet.smul_prod_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T05:51:23.296302+00:00
-- url     : https://prove2.me/theorems/00c7d2ae-d424-4130-a2d6-6f042acf338f
-- title:
--   Tile Set: smul prod one
-- statement:
--   The Tile Set construction uses the smul prod one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/TileSet.lean#L315-L316
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/TileSet.lean#L315-L316

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

theorem DiscreteTiling.TileSet.smul_prod_one (g : G) (t : TileSet ps ιₜ) : (g, (1 : Equiv.Perm ιₜ)) • t = g • t := by sorry

attribute [defeq] DiscreteTiling.TileSet.smul_prod_one
