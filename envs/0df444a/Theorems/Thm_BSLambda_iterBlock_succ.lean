-- Prove2me | Theorems.Thm_BSLambda_iterBlock_succ
-- name    : BSLambda.iterBlock_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:35:28.827002+00:00
-- url     : https://prove2.me/theorems/6cbc79d2-a42a-4197-a98b-65a5df0bba6d
-- title:
--   BSLambda: iter Block succ
-- statement:
--   The recursion equation of `iterBlock`: the first index picks the outer factor.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Composition.lean#L90-L91
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Composition.lean#L90-L91

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Sensitivity
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Composition
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open Function
universe u

theorem BSLambda.iterBlock_succ {V ι : Type*} [DecidableEq V] (blk : ι → Finset V) (m : ℕ)
    (t : IterCoord ι (m + 1)) : iterBlock blk (m + 1) t = blk t.1 ×ˢ iterBlock blk m t.2 := by sorry
