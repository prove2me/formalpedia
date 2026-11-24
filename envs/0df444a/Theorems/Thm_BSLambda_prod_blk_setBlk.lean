-- Prove2me | Theorems.Thm_BSLambda_prod_blk_setBlk
-- name    : BSLambda.prod_blk_setBlk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:20:23.338717+00:00
-- url     : https://prove2.me/theorems/24014aad-678b-491e-9cf7-a58e4b6fa66c
-- title:
--   BSLambda: prod blk set Blk
-- statement:
--   Overwriting the `w`-th block changes exactly one factor of a product over the blocks.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Multiplicative.lean#L124-L131
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Multiplicative.lean#L124-L131

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

theorem BSLambda.prod_blk_setBlk {M : Type*} [Fintype W] [CommMonoid M]
    (u : Input V → M) (x : Input (W × V)) (w : W) (z : Input V) :
    ∏ w' : W, u (blk (setBlk x w z) w') = u z * ∏ w' ∈ Finset.univ.erase w, u (blk x w') := by sorry
