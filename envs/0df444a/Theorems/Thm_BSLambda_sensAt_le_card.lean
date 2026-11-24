-- Prove2me | Theorems.Thm_BSLambda_sensAt_le_card
-- name    : BSLambda.sensAt_le_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:51:42.641575+00:00
-- url     : https://prove2.me/theorems/04c710da-8b17-44a8-86a6-1f5699fad818
-- title:
--   BSLambda: sens At le card
-- statement:
--   Any `Finset` containing every sensitive coordinate at `x` bounds `s(f,x)`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Sensitivity.lean#L68-L70
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Sensitivity.lean#L68-L70

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Sensitivity
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BSLambda.sensAt_le_card {f : Input V → Bool} {x : Input V} {s : Finset V}
    (h : sensCoords f x ⊆ s) : sensAt f x ≤ s.card := by sorry
