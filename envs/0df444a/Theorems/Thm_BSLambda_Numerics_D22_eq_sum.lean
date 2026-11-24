-- Prove2me | Theorems.Thm_BSLambda_Numerics_D22_eq_sum
-- name    : BSLambda.Numerics.D22_eq_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:54:28.516801+00:00
-- url     : https://prove2.me/theorems/65f7e432-38f2-421c-b3b9-19e528691845
-- title:
--   Numerics: D22 eq sum
-- statement:
--   `D₂₂` is the Section 10.1 sum it abbreviates; the evaluation is `depSumTwoTwo_eq`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Numerics/LLLBounds.lean#L86-L88
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Numerics/LLLBounds.lean#L86-L88

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Binomial
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Logs
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_LLLBounds
set_option autoImplicit true
@[expose] public section
public section
open BSLambda BSLambda.Numerics

theorem BSLambda.Numerics.D22_eq_sum :
    D22 = (∑ s ∈ Finset.Icc 2 9, Nat.choose 9 s * Nat.choose 14002 (9 - s)) - 1 := by sorry
