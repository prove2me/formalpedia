-- Prove2me | Theorems.Thm_BSLambda_iterBlock_zero
-- name    : BSLambda.iterBlock_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:47:20.245729+00:00
-- url     : https://prove2.me/theorems/e36b5368-50f7-4177-8e48-990f137dfcab
-- title:
--   BSLambda: iter Block zero
-- statement:
--   There is a single degenerate `0`-fold product block, the whole (one-point) cube.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Composition.lean#L86-L87
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Composition.lean#L86-L87

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Sensitivity
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Composition
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open Function
universe u

theorem BSLambda.iterBlock_zero {V ι : Type*} [DecidableEq V] (blk : ι → Finset V)
    (t : IterCoord ι 0) : iterBlock blk 0 t = (Finset.univ : Finset PUnit) := by sorry

attribute [defeq] BSLambda.iterBlock_zero
