-- Prove2me | Theorems.Thm_BSLambda_LLL_Flag1_Active_card_nonOwners
-- name    : BSLambda.LLL.Flag1.Active.card_nonOwners
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:03:16.177135+00:00
-- url     : https://prove2.me/theorems/01370c54-313c-4664-8efa-57129d4828c0
-- title:
--   Active: card non Owners
-- statement:
--   An active flag has exactly four non-owners.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L452-L457
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L452-L457

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
open BSLambda.LLL.Flag1.Active
variable (hF : F.Active Arc)
include hF

theorem BSLambda.LLL.Flag1.Active.card_nonOwners : F.nonOwners.card = 4 := by sorry
