-- Prove2me | Theorems.Thm_BSLambda_sensAt_le_sens
-- name    : BSLambda.sensAt_le_sens
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:55:11.085123+00:00
-- url     : https://prove2.me/theorems/a8119728-9f35-4968-81e0-d5e0c64eaceb
-- title:
--   BSLambda: sens At le sens
-- statement:
--   The BSLambda construction uses the sens At le sens property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Sensitivity.lean#L80-L81
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Sensitivity.lean#L80-L81

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Sensitivity
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BSLambda.sensAt_le_sens (f : Input V → Bool) (x : Input V) : sensAt f x ≤ sens f := by sorry
