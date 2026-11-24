-- Prove2me | Theorems.Thm_BSLambda_LLL_badX_pos
-- name    : BSLambda.LLL.badX_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:08:46.537175+00:00
-- url     : https://prove2.me/theorems/f9a4b5c4-1fe3-4c6d-9ca4-701b57e61b7e
-- title:
--   LLL: bad X pos
-- statement:
--   The weights are positive.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/GateExists.lean#L774-L777
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/GateExists.lean#L774-L777

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Obstruction
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_LLLBounds
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_GateExists
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.LLL
open Numerics Construction
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {r : ℕ} {Arc : ι → ι → Bool}

theorem BSLambda.LLL.badX_pos (t : Bool) : 0 < badX t := by sorry
