-- Prove2me | Theorems.Thm_BSLambda_flipSet_prod_singleton
-- name    : BSLambda.flipSet_prod_singleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:14:18.894228+00:00
-- url     : https://prove2.me/theorems/993896c8-22ec-4e6c-9038-2cf8f2979e11
-- title:
--   BSLambda: flip Set prod singleton
-- statement:
--   Flipping the coordinate `(w, v)` flips the coordinate `v` inside the `w`-th block.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Multiplicative.lean#L134-L146
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Multiplicative.lean#L134-L146

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_OpNorm
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Composition
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Multiplicative
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open scoped Matrix
variable {W V : Type*}
variable [DecidableEq W]

theorem BSLambda.flipSet_prod_singleton [DecidableEq V] (x : Input (W × V)) (w : W) (v : V) :
    flipSet x {(w, v)} = setBlk x w (flipSet (blk x w) {v}) := by sorry
