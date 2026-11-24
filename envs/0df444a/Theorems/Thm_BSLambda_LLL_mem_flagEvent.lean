-- Prove2me | Theorems.Thm_BSLambda_LLL_mem_flagEvent
-- name    : BSLambda.LLL.mem_flagEvent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:01:37.42006+00:00
-- url     : https://prove2.me/theorems/66e4e6e6-e3e3-45ba-b256-50001d238bcf
-- title:
--   LLL: mem flag Event
-- statement:
--   The LLL construction uses the mem flag Event property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L499-L502
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L499-L502

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

theorem BSLambda.LLL.mem_flagEvent {Arc : ι → ι → Bool} {F : Flag1 ι} {ω : GateCfg ι r} :
    ω ∈ flagEvent Arc F ↔ ∀ p ∈ arcSet Arc F.nonOwners, ω p = ω (F.owner, p.2) := by sorry
