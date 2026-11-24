-- Prove2me | Theorems.Thm_BSLambda_topBits_setBlk_ne
-- name    : BSLambda.topBits_setBlk_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:20:35.451625+00:00
-- url     : https://prove2.me/theorems/36d232df-d511-4467-906a-2fe920fb2bf7
-- title:
--   BSLambda: top Bits set Blk ne
-- statement:
--   If the top bits of `x` disagree with `c` at some coordinate other than `w`, then no
--   rewriting of the `w`-th block lands in the fibre of `topBits g` over `c`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Multiplicative.lean#L180-L184
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Multiplicative.lean#L180-L184

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

theorem BSLambda.topBits_setBlk_ne (g : Input V → Bool) (x : Input (W × V)) (w : W) {c : Input W}
    {w' : W} (hw' : w' ≠ w) (h : topBits g x w' ≠ c w') (z : Input V) :
    topBits g (setBlk x w z) ≠ c := by sorry
