-- Prove2me | Theorems.Thm_BSLambda_LLL_Flag1_Active_owner_notMem_nonOwners
-- name    : BSLambda.LLL.Flag1.Active.owner_notMem_nonOwners
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:01:07.250436+00:00
-- url     : https://prove2.me/theorems/9dfd1c11-c77e-49a7-b458-a3d689121118
-- title:
--   Active: owner not Mem non Owners
-- statement:
--   The owner of an active flag is not one of its non-owners.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L416-L416
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L416-L416

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

theorem BSLambda.LLL.Flag1.Active.owner_notMem_nonOwners : F.owner ∉ F.nonOwners := by sorry
