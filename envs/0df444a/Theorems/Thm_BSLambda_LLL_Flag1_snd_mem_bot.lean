-- Prove2me | Theorems.Thm_BSLambda_LLL_Flag1_snd_mem_bot
-- name    : BSLambda.LLL.Flag1.snd_mem_bot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:03:21.978801+00:00
-- url     : https://prove2.me/theorems/28ee59bf-c36a-4b47-82a1-432815ccc502
-- title:
--   Flag1: snd mem bot
-- statement:
--   Every non-owner arc of an active flag has its head in `F.bot`, so the owner's gate into
--   that head block is defined; and its tail is not the owner, so its label is a variable
--   distinct from the conditioned owner gates.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L482-L490
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L482-L490

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Asymmetric
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Basic
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Binomial
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Obstruction
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.LLL
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {r : ℕ}
omit [Fintype ι]

theorem BSLambda.LLL.Flag1.snd_mem_bot (F : Flag1 ι) {Arc : ι → ι → Bool} (hT : IsTournament Arc)
    (hF : F.Active Arc) {p : ι × ι} (hp : p ∈ arcSet Arc F.nonOwners) : p.2 ∈ F.bot := by sorry
