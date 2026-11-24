-- Prove2me | Theorems.Thm_BSLambda_bsAt_le_bs
-- name    : BSLambda.bsAt_le_bs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:51:49.73883+00:00
-- url     : https://prove2.me/theorems/49c3a830-7725-469a-8714-4b06b2123e94
-- title:
--   BSLambda: bs At le bs
-- statement:
--   The BSLambda construction uses the bs At le bs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Sensitivity.lean#L128-L129
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Sensitivity.lean#L128-L129

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Sensitivity
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BSLambda.bsAt_le_bs (f : Input V → Bool) (x : Input V) : bsAt f x ≤ bs f := by sorry
