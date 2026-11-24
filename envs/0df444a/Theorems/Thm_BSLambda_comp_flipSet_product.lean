-- Prove2me | Theorems.Thm_BSLambda_comp_flipSet_product
-- name    : BSLambda.comp_flipSet_product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:54:50.816814+00:00
-- url     : https://prove2.me/theorems/840d4ae9-6204-4e39-9a81-1400a86a979b
-- title:
--   BSLambda: comp flip Set product
-- statement:
--   The key composition step of Section 14: if the inner function `g` is flipped from `0`
--   to `1` by the block `B`, then `comp f g` on the product block `A ×ˢ B` feeds `f` exactly
--   the all-zero input flipped on `A`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Composition.lean#L119-L127
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Composition.lean#L119-L127

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Sensitivity
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Composition
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open Function
universe u

theorem BSLambda.comp_flipSet_product {V W : Type*} [DecidableEq V] [DecidableEq W]
    {f : Input V → Bool} {g : Input W → Bool} {A : Finset V} {B : Finset W}
    (hzero : g (zeroInput W) = false) (hflip : g (flipSet (zeroInput W) B) = true) :
    comp f g (flipSet (zeroInput (V × W)) (A ×ˢ B)) = f (flipSet (zeroInput V) A) := by sorry
