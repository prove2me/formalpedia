-- Prove2me | Theorems.Thm_BSLambda_LLL_Flag1_Active_arc_top_owner
-- name    : BSLambda.LLL.Flag1.Active.arc_top_owner
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:01:11.334803+00:00
-- url     : https://prove2.me/theorems/9eb6cb07-1677-4287-9068-9baf5698f726
-- title:
--   Active: arc top owner
-- statement:
--   The second top vertex of an active flag beats the owner.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L438-L439
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L438-L439

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

theorem BSLambda.LLL.Flag1.Active.arc_top_owner (ha : F.top = some a) : Arc a F.owner = true := by sorry
