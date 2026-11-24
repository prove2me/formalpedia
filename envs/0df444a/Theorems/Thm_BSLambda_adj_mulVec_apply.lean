-- Prove2me | Theorems.Thm_BSLambda_adj_mulVec_apply
-- name    : BSLambda.adj_mulVec_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:59:20.870891+00:00
-- url     : https://prove2.me/theorems/833b6ec7-8de5-4ec2-ba0a-fb0079bf8264
-- title:
--   BSLambda: adj mul Vec apply
-- statement:
--   `A_f *ᵥ v` written as a sum over coordinate flips.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/OpNorm.lean#L135-L148
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/OpNorm.lean#L135-L148

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Bipartite
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_OpNorm
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open scoped Matrix Matrix.Norms.L2Operator
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BSLambda.adj_mulVec_apply (f : Input V → Bool) (ν : Input V → ℝ) (x : Input V) :
    (adj f *ᵥ ν) x = ∑ i : V, adj f x (flipSet x {i}) * ν (flipSet x {i}) := by sorry
