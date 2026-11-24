-- Prove2me | Theorems.Thm_BSLambda_topBits_setBlk_of_ne
-- name    : BSLambda.topBits_setBlk_of_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:16:19.725131+00:00
-- url     : https://prove2.me/theorems/17724bfb-86d5-46e7-b130-7d67b4877316
-- title:
--   BSLambda: top Bits set Blk of ne
-- statement:
--   Rewriting the `w`-th block so as to change its `g`-value flips the `w`-th top bit.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Multiplicative.lean#L168-L176
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Multiplicative.lean#L168-L176

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

theorem BSLambda.topBits_setBlk_of_ne (g : Input V → Bool) (x : Input (W × V)) (w : W) (z : Input V)
    (h : g z ≠ g (blk x w)) :
    topBits g (setBlk x w z) = flipSet (topBits g x) {w} := by sorry
