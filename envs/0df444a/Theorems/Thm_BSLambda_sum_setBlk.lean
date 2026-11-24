-- Prove2me | Theorems.Thm_BSLambda_sum_setBlk
-- name    : BSLambda.sum_setBlk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:20:54.227478+00:00
-- url     : https://prove2.me/theorems/1c35a4bc-881b-4be5-b52e-f4da5dde35aa
-- title:
--   BSLambda: sum set Blk
-- statement:
--   Every input decomposes as a value for the `w`-th block together with an input whose `w`-th
--   block is zero, so a sum over all inputs splits accordingly.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Multiplicative.lean#L281-L286
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Multiplicative.lean#L281-L286

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

theorem BSLambda.sum_setBlk (w : W) (F : Input (W × V) → ℝ) :
    ∑ y : {x : Input (W × V) // blk x w = zeroInput V}, ∑ a : Input V, F (setBlk y.1 w a)
      = ∑ x : Input (W × V), F x := by sorry
