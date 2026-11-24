-- Prove2me | Theorems.Thm_BSLambda_LLL_Flag1_Active_owner_ne_top
-- name    : BSLambda.LLL.Flag1.Active.owner_ne_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:01:35.339032+00:00
-- url     : https://prove2.me/theorems/58003864-9d01-4a0a-a34b-5949e7325b08
-- title:
--   Active: owner ne top
-- statement:
--   The owner of an active flag differs from its second top vertex.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L430-L431
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L430-L431

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

theorem BSLambda.LLL.Flag1.Active.owner_ne_top (ha : F.top = some a) : F.owner ≠ a := by sorry
