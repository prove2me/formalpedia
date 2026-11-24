-- Prove2me | Theorems.Thm_BSLambda_LLL_Flag1_Active_arc_owner_bot
-- name    : BSLambda.LLL.Flag1.Active.arc_owner_bot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:00:02.277598+00:00
-- url     : https://prove2.me/theorems/4deddb2d-0d6d-4d6d-9388-3ea4b7277491
-- title:
--   Active: arc owner bot
-- statement:
--   The owner of an active flag dominates every bottom vertex, in both patterns.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L442-L445
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L442-L445

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

theorem BSLambda.LLL.Flag1.Active.arc_owner_bot (hj : j ∈ F.bot) : Arc F.owner j = true := by sorry
