-- Prove2me | Theorems.Thm_BSLambda_topBits_setBlk_of_eq
-- name    : BSLambda.topBits_setBlk_of_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:20:25.167136+00:00
-- url     : https://prove2.me/theorems/d929a5a5-f686-4dd1-b336-9aeeed1e8629
-- title:
--   BSLambda: top Bits set Blk of eq
-- statement:
--   Rewriting the `w`-th block without changing its `g`-value leaves the top bits alone.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Multiplicative.lean#L160-L165
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Multiplicative.lean#L160-L165

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

theorem BSLambda.topBits_setBlk_of_eq (g : Input V → Bool) (x : Input (W × V)) (w : W) (z : Input V)
    (h : g z = g (blk x w)) :
    topBits g (setBlk x w z) = topBits g x := by sorry
