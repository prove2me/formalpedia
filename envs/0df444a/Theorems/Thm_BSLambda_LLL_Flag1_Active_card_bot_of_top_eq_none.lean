-- Prove2me | Theorems.Thm_BSLambda_LLL_Flag1_Active_card_bot_of_top_eq_none
-- name    : BSLambda.LLL.Flag1.Active.card_bot_of_top_eq_none
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:01:25.294028+00:00
-- url     : https://prove2.me/theorems/989a00ea-9e95-4dec-b23c-8e506948cc69
-- title:
--   Active: card bot of top eq none
-- statement:
--   An active `Type A` flag has four bottom vertices.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L422-L423
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L422-L423

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

theorem BSLambda.LLL.Flag1.Active.card_bot_of_top_eq_none (ha : F.top = none) : F.bot.card = 4 := by sorry
