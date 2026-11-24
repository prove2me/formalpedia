-- Prove2me | Theorems.Thm_BSLambda_flipSet_zeroInput_product_slice
-- name    : BSLambda.flipSet_zeroInput_product_slice
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:54:45.530723+00:00
-- url     : https://prove2.me/theorems/381e8abd-3d69-44f0-acb2-b59a6ae1aa19
-- title:
--   BSLambda: flip Set zero Input product slice
-- statement:
--   Slicing the all-zero input flipped on a product block `A ×ˢ B`: the `v`-slice is the
--   flip of `B` when `v ∈ A`, and the all-zero input otherwise (Section 14).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Composition.lean#L109-L114
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Composition.lean#L109-L114

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Sensitivity
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Composition
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open Function
universe u

theorem BSLambda.flipSet_zeroInput_product_slice {V W : Type*} [DecidableEq V] [DecidableEq W]
    (A : Finset V) (B : Finset W) (v : V) :
    (fun w => flipSet (zeroInput (V × W)) (A ×ˢ B) (v, w))
      = if v ∈ A then flipSet (zeroInput W) B else zeroInput W := by sorry
