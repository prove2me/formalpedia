-- Prove2me | Theorems.Thm_BSLambda_LLL_Flag1_Active_top_notMem_bot
-- name    : BSLambda.LLL.Flag1.Active.top_notMem_bot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:06:27.640136+00:00
-- url     : https://prove2.me/theorems/3951bf8a-d4e0-4401-8819-7758e06e8a09
-- title:
--   Active: top not Mem bot
-- statement:
--   The second top vertex of an active flag is not a bottom vertex.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L434-L435
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L434-L435

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

theorem BSLambda.LLL.Flag1.Active.top_notMem_bot (ha : F.top = some a) : a ∉ F.bot := by sorry
