-- Prove2me | Theorems.Thm_BSLambda_LLL_headOut_none
-- name    : BSLambda.LLL.headOut_none
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:59:53.300963+00:00
-- url     : https://prove2.me/theorems/4109da23-47aa-4b54-8161-90eb8d4ef0ea
-- title:
--   LLL: head Out none
-- statement:
--   The common out-neighbourhood of a Type-A head is the out-neighbourhood of the owner.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/GateExists.lean#L330-L330
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/GateExists.lean#L330-L330

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

theorem BSLambda.LLL.headOut_none (o : ι) : headOut Arc (o, none) = outNbrs Arc o := by sorry

attribute [defeq] BSLambda.LLL.headOut_none
