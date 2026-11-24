-- Prove2me | Theorems.Thm_BSLambda_LLL_badX_lt_one
-- name    : BSLambda.LLL.badX_lt_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:08:51.231368+00:00
-- url     : https://prove2.me/theorems/5f5fd5b5-892e-4fa1-b7e4-eabb32afc9e1
-- title:
--   LLL: bad X lt one
-- statement:
--   The weights are less than one.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/GateExists.lean#L780-L783
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/GateExists.lean#L780-L783

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

theorem BSLambda.LLL.badX_lt_one (t : Bool) : badX t < 1 := by sorry
