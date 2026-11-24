-- Prove2me | Theorems.Thm_BSLambda_adj_comp_flip
-- name    : BSLambda.adj_comp_flip
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:20:32.412622+00:00
-- url     : https://prove2.me/theorems/5aaaf85a-371b-46fc-ae8c-e21b6f84cf43
-- title:
--   BSLambda: adj comp flip
-- statement:
--   An edge of the sensitivity graph of `comp f g` is a `g`-sensitive flip inside one block
--   whose effect on the top bits is an `f`-sensitive flip.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Multiplicative.lean#L206-L223
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Multiplicative.lean#L206-L223

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_OpNorm
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Composition
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Multiplicative
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open scoped Matrix
variable {W V : Type*} [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V]

theorem BSLambda.adj_comp_flip (f : Input W → Bool) (g : Input V → Bool) (x : Input (W × V)) (w : W)
    (v : V) :
    adj (comp f g) x (flipSet x {(w, v)})
      = adj f (topBits g x) (flipSet (topBits g x) {w})
        * adj g (blk x w) (flipSet (blk x w) {v}) := by sorry
