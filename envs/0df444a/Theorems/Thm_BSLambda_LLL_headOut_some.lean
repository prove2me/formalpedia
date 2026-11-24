-- Prove2me | Theorems.Thm_BSLambda_LLL_headOut_some
-- name    : BSLambda.LLL.headOut_some
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:59:54.682805+00:00
-- url     : https://prove2.me/theorems/3166a383-8bc0-4e68-8398-6d0260c75179
-- title:
--   LLL: head Out some
-- statement:
--   The common out-neighbourhood of a Type-B head is the set of common out-neighbours of the
--   owner and the top vertex.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/GateExists.lean#L334-L334
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/GateExists.lean#L334-L334

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

theorem BSLambda.LLL.headOut_some (o a : ι) : headOut Arc (o, some a) = commonOut Arc o a := by sorry

attribute [defeq] BSLambda.LLL.headOut_some
