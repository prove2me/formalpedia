-- Prove2me | Theorems.Thm_BSLambda_LLL_mem_ownerGates
-- name    : BSLambda.LLL.mem_ownerGates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:59:21.731411+00:00
-- url     : https://prove2.me/theorems/bc350f1a-7aab-40c5-ac86-1c03bb256be8
-- title:
--   LLL: mem owner Gates
-- statement:
--   The LLL construction uses the mem owner Gates property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L82-L84
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L82-L84

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
omit [Fintype ι] [DecidableEq ι]

theorem BSLambda.LLL.mem_ownerGates {i : ι} {T : Finset ι} {p : ι × ι} :
    p ∈ ownerGates i T ↔ p.1 = i ∧ p.2 ∈ T := by sorry
