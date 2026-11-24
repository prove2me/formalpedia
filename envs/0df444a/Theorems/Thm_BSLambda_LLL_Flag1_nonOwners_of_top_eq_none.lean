-- Prove2me | Theorems.Thm_BSLambda_LLL_Flag1_nonOwners_of_top_eq_none
-- name    : BSLambda.LLL.Flag1.nonOwners_of_top_eq_none
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:01:06.031444+00:00
-- url     : https://prove2.me/theorems/42df50f3-1588-4b82-96c3-ef9f22ef256c
-- title:
--   Flag1: non Owners of top eq none
-- statement:
--   The Flag1 construction uses the non Owners of top eq none property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L366-L367
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L366-L367

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

theorem BSLambda.LLL.Flag1.nonOwners_of_top_eq_none (ha : F.top = none) : F.nonOwners = F.bot := by sorry
