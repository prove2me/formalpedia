-- Prove2me | Theorems.Thm_BSLambda_LLL_Flag1_Active_card_bot_of_top_eq_some
-- name    : BSLambda.LLL.Flag1.Active.card_bot_of_top_eq_some
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:00:37.572809+00:00
-- url     : https://prove2.me/theorems/9b3060ed-526a-42c6-bd71-dbff4eda4fca
-- title:
--   Active: card bot of top eq some
-- statement:
--   An active `Type B` flag has three bottom vertices.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L426-L427
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L426-L427

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

theorem BSLambda.LLL.Flag1.Active.card_bot_of_top_eq_some (ha : F.top = some a) : F.bot.card = 3 := by sorry
