-- Prove2me | Theorems.Thm_BSLambda_LLL_Flag1_nonOwners_of_top_eq_some
-- name    : BSLambda.LLL.Flag1.nonOwners_of_top_eq_some
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:01:03.964789+00:00
-- url     : https://prove2.me/theorems/522e9951-275c-43e8-9137-255c84edb82e
-- title:
--   Flag1: non Owners of top eq some
-- statement:
--   The Flag1 construction uses the non Owners of top eq some property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L369-L370
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L369-L370

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

theorem BSLambda.LLL.Flag1.nonOwners_of_top_eq_some (ha : F.top = some a) : F.nonOwners = insert a F.bot := by sorry
