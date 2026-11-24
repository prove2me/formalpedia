-- Prove2me | Theorems.Thm_BSLambda_sens_le
-- name    : BSLambda.sens_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:55:16.03461+00:00
-- url     : https://prove2.me/theorems/9642c66a-dcd9-4be0-9b0b-9c2c10276ae0
-- title:
--   BSLambda: sens le
-- statement:
--   The BSLambda construction uses the sens le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Sensitivity.lean#L83-L84
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Sensitivity.lean#L83-L84

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Sensitivity
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BSLambda.sens_le (f : Input V → Bool) {n : ℕ} (h : ∀ x, sensAt f x ≤ n) : sens f ≤ n := by sorry
