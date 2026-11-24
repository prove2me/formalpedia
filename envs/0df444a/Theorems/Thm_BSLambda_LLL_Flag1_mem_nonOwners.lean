-- Prove2me | Theorems.Thm_BSLambda_LLL_Flag1_mem_nonOwners
-- name    : BSLambda.LLL.Flag1.mem_nonOwners
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:59:39.222401+00:00
-- url     : https://prove2.me/theorems/b7f0d342-b455-4c00-b02e-5cd28bc814a5
-- title:
--   Flag1: mem non Owners
-- statement:
--   The Flag1 construction uses the mem non Owners property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L372-L375
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L372-L375

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
open BSLambda.LLL.Flag1
omit [Fintype ι]
variable {F : Flag1 ι} {Arc : ι → ι → Bool} {a j : ι} {p : ι × ι}

theorem BSLambda.LLL.Flag1.mem_nonOwners : j ∈ F.nonOwners ↔ j ∈ F.top ∨ j ∈ F.bot := by sorry
