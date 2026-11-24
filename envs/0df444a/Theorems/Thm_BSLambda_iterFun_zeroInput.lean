-- Prove2me | Theorems.Thm_BSLambda_iterFun_zeroInput
-- name    : BSLambda.iterFun_zeroInput
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:51:13.851377+00:00
-- url     : https://prove2.me/theorems/f1269727-7ab6-4bac-b34e-1ce769034291
-- title:
--   BSLambda: iter Fun zero Input
-- statement:
--   The all-zero input of `F_m` evaluates to `0` whenever the seed does (Section 14).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Composition.lean#L135-L141
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Composition.lean#L135-L141

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Sensitivity
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Composition
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open Function
universe u
variable {V ι : Type*} [DecidableEq V] {f : Input V → Bool} {blk : ι → Finset V}
omit [DecidableEq V]

theorem BSLambda.iterFun_zeroInput (hzero : f (zeroInput V) = false) :
    ∀ m, iterFun f m (zeroInput (IterCoord V m)) = false
  := by sorry
