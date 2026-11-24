-- Prove2me | Theorems.Thm_BSLambda_sensAt_eq_card_univ
-- name    : BSLambda.sensAt_eq_card_univ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:51:43.120475+00:00
-- url     : https://prove2.me/theorems/4821e875-428d-4c9f-82a5-6aacfd94d024
-- title:
--   BSLambda: sens At eq card univ
-- statement:
--   If every coordinate is sensitive at `x` then `s(f,x)` counts all coordinates.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Sensitivity.lean#L73-L75
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Sensitivity.lean#L73-L75

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Sensitivity
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BSLambda.sensAt_eq_card_univ {f : Input V → Bool} {x : Input V} (h : ∀ v, SensitiveCoord f x v) :
    sensAt f x = Fintype.card V := by sorry
