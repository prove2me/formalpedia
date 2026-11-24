-- Prove2me | Theorems.Thm_BSLambda_LLL_exists_inl_of_badTy_eq_false
-- name    : BSLambda.LLL.exists_inl_of_badTy_eq_false
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:07:51.627199+00:00
-- url     : https://prove2.me/theorems/fcab2c02-e474-4a27-8424-90323c9087f7
-- title:
--   LLL: exists inl of bad Ty eq false
-- statement:
--   A bad event of type `false` is an active radius-one flag.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/GateExists.lean#L81-L85
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/GateExists.lean#L81-L85

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Obstruction
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_LLLBounds
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_GateExists
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.LLL
open Numerics Construction
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {r : ℕ} {Arc : ι → ι → Bool}
omit [Fintype ι]

theorem BSLambda.LLL.exists_inl_of_badTy_eq_false {j : BadIdx Arc} (hj : badTy j = false) :
    ∃ F : {F : Flag1 ι // F.Active Arc}, j = Sum.inl F := by sorry
