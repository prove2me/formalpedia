-- Prove2me | Theorems.Thm_BSLambda_blockFamilyCards_bddAbove
-- name    : BSLambda.blockFamilyCards_bddAbove
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:51:44.724799+00:00
-- url     : https://prove2.me/theorems/c82dea25-d0bb-4fbe-bd30-404e3e8807e7
-- title:
--   BSLambda: block Family Cards bdd Above
-- statement:
--   The BSLambda construction uses the block Family Cards bdd Above property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Sensitivity.lean#L109-L114
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Sensitivity.lean#L109-L114

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Sensitivity
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [Fintype V]

theorem BSLambda.blockFamilyCards_bddAbove [Finite V] (f : Input V → Bool) (x : Input V) :
    BddAbove (blockFamilyCards f x) := by sorry
