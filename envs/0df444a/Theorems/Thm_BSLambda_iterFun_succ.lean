-- Prove2me | Theorems.Thm_BSLambda_iterFun_succ
-- name    : BSLambda.iterFun_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:35:33.980825+00:00
-- url     : https://prove2.me/theorems/13ada909-c771-4b9c-8409-6619fb0632d1
-- title:
--   BSLambda: iter Fun succ
-- statement:
--   The recursion equation of `iterFun`: `F_{m+1} = f ∘ F_m`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Composition.lean#L104-L105
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Composition.lean#L104-L105

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Sensitivity
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Composition
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open Function
universe u

theorem BSLambda.iterFun_succ {V : Type*} (f : Input V → Bool) (m : ℕ) :
    iterFun f (m + 1) = comp f (iterFun f m) := by sorry
