-- Prove2me | Theorems.Thm_BSLambda_topBits_setBlk_eq_iff
-- name    : BSLambda.topBits_setBlk_eq_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:20:38.202275+00:00
-- url     : https://prove2.me/theorems/8d8e8bfa-26a1-4fac-a964-87387ff82cd5
-- title:
--   BSLambda: top Bits set Blk eq iff
-- statement:
--   If the top bits of `x` already agree with `c` away from `w`, then `setBlk x w z` lies in the
--   fibre of `topBits g` over `c` exactly when `g z` is the `w`-th bit of `c`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Multiplicative.lean#L188-L194
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Multiplicative.lean#L188-L194

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

theorem BSLambda.topBits_setBlk_eq_iff (g : Input V → Bool) (x : Input (W × V)) (w : W) {c : Input W}
    (hc : ∀ w' : W, w' ≠ w → topBits g x w' = c w') (z : Input V) :
    topBits g (setBlk x w z) = c ↔ g z = c w := by sorry
