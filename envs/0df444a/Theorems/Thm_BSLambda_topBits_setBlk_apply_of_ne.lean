-- Prove2me | Theorems.Thm_BSLambda_topBits_setBlk_apply_of_ne
-- name    : BSLambda.topBits_setBlk_apply_of_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:14:11.30037+00:00
-- url     : https://prove2.me/theorems/fa8879fa-0035-4b3c-90fb-836491832aa0
-- title:
--   BSLambda: top Bits set Blk apply of ne
-- statement:
--   Away from `w`, the top bits of `setBlk x w z` are those of `x`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Multiplicative.lean#L154-L157
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Multiplicative.lean#L154-L157

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

theorem BSLambda.topBits_setBlk_apply_of_ne (g : Input V → Bool) (x : Input (W × V)) (w : W)
    (z : Input V) {w' : W} (h : w' ≠ w) :
    topBits g (setBlk x w z) w' = topBits g x w' := by sorry
