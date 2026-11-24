-- Prove2me | Theorems.Thm_BSLambda_Construction_block_disjoint
-- name    : BSLambda.Construction.block_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:50:42.948726+00:00
-- url     : https://prove2.me/theorems/472a887f-c82b-40d0-b3e4-bee84b07c09b
-- title:
--   Construction: block disjoint
-- statement:
--   The Construction construction uses the block disjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Construction/Basic.lean#L63-L65
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Construction/Basic.lean#L63-L65

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Sensitivity
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Subcube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Tournament
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Basic
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.Construction
variable {ι : Type*} {r : ℕ}

theorem BSLambda.Construction.block_disjoint {i j : ι} (h : i ≠ j) :
    Disjoint (block i : Finset (Coord ι r)) (block j) := by sorry
