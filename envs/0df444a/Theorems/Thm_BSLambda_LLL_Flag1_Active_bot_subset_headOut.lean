-- Prove2me | Theorems.Thm_BSLambda_LLL_Flag1_Active_bot_subset_headOut
-- name    : BSLambda.LLL.Flag1.Active.bot_subset_headOut
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:00:13.744552+00:00
-- url     : https://prove2.me/theorems/6b9711dd-ffdf-4782-adc5-e930dedee829
-- title:
--   Active: bot subset head Out
-- statement:
--   The bottom set of an active flag lies in the common out-neighbourhood of its head.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/GateExists.lean#L337-L341
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/GateExists.lean#L337-L341

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

theorem BSLambda.LLL.Flag1.Active.bot_subset_headOut {G : Flag1 ι} (hG : G.Active Arc) :
    G.bot ⊆ headOut Arc (G.owner, G.top) := by sorry
