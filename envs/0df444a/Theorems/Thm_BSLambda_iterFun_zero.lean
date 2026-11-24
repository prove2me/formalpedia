-- Prove2me | Theorems.Thm_BSLambda_iterFun_zero
-- name    : BSLambda.iterFun_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:47:29.159861+00:00
-- url     : https://prove2.me/theorems/f8145999-70f0-4466-94e3-05416c55fcd0
-- title:
--   BSLambda: iter Fun zero
-- statement:
--   `F_0` is the one-bit identity function.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Composition.lean#L100-L101
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Composition.lean#L100-L101

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Sensitivity
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Composition
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open Function
universe u

theorem BSLambda.iterFun_zero {V : Type*} (f : Input V → Bool) (x : Input (IterCoord V 0)) :
    iterFun f 0 x = x PUnit.unit := by sorry

attribute [defeq] BSLambda.iterFun_zero
