-- Prove2me | Theorems.Thm_BSLambda_topBits_setBlk_apply_self
-- name    : BSLambda.topBits_setBlk_apply_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:14:21.166747+00:00
-- url     : https://prove2.me/theorems/59f32696-7967-4af1-81f5-a89bd2b83136
-- title:
--   BSLambda: top Bits set Blk apply self
-- statement:
--   The `w`-th top bit of `setBlk x w z` is the value of `g` on the new block.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Multiplicative.lean#L149-L151
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Multiplicative.lean#L149-L151

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

theorem BSLambda.topBits_setBlk_apply_self (g : Input V → Bool) (x : Input (W × V)) (w : W)
    (z : Input V) : topBits g (setBlk x w z) w = g z := by sorry
