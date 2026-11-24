-- Prove2me | Theorems.Thm_BSLambda_LLL_Flag1_Active_arc_top_bot
-- name    : BSLambda.LLL.Flag1.Active.arc_top_bot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:00:38.174204+00:00
-- url     : https://prove2.me/theorems/11716472-10c4-4e9d-890d-8c149788833b
-- title:
--   Active: arc top bot
-- statement:
--   The second top vertex of an active flag dominates every bottom vertex.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L448-L449
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L448-L449

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

theorem BSLambda.LLL.Flag1.Active.arc_top_bot (ha : F.top = some a) (hj : j ∈ F.bot) : Arc a j = true := by sorry
