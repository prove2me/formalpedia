-- Prove2me | Theorems.Thm_BSLambda_comp_apply
-- name    : BSLambda.comp_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:54:40.604029+00:00
-- url     : https://prove2.me/theorems/baa3561f-9bea-4b18-a34b-ccf25b1b7866
-- title:
--   BSLambda: comp apply
-- statement:
--   The defining equation of `comp`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Composition.lean#L46-L47
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Composition.lean#L46-L47

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Sensitivity
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Composition
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open Function
universe u

theorem BSLambda.comp_apply {W V : Type*} (f : Input W → Bool) (g : Input V → Bool)
    (x : Input (W × V)) : comp f g x = f fun w ↦ g fun v ↦ x (w, v) := by sorry
