-- Prove2me | Theorems.Thm_BSLambda_adj_apply_eq_ite_mem_nbrs
-- name    : BSLambda.adj_apply_eq_ite_mem_nbrs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:04:47.968883+00:00
-- url     : https://prove2.me/theorems/447ca8c8-9a67-422a-8386-169e97486c66
-- title:
--   BSLambda: adj apply eq ite mem nbrs
-- statement:
--   `adj f x y` is the indicator of `y` being a neighbour of `x` in `G_f`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Spectral.lean#L100-L102
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Spectral.lean#L100-L102

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Sensitivity
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Hermitian
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Spectral
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open scoped Matrix Matrix.Norms.L2Operator
variable {V : Type*} [Fintype V]
variable [DecidableEq V]

theorem BSLambda.adj_apply_eq_ite_mem_nbrs (f : Input V → Bool) (x y : Input V) :
    adj f x y = if y ∈ nbrs f x then 1 else 0 := by sorry
