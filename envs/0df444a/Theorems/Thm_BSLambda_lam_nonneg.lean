-- Prove2me | Theorems.Thm_BSLambda_lam_nonneg
-- name    : BSLambda.lam_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:58:13.574949+00:00
-- url     : https://prove2.me/theorems/0e9bb9d0-9fe1-4f10-b207-54ce3c8b78e7
-- title:
--   BSLambda: lam nonneg
-- statement:
--   `lambda(f) ≥ 0`: the eigenvalues of `adj f` sum to `trace (adj f) = 0`, so at least one of
--   them, hence their supremum, is nonnegative (Section 11.1 of `bs_lambda.txt`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Spectral.lean#L124-L130
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Spectral.lean#L124-L130

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

theorem BSLambda.lam_nonneg (f : Input V → Bool) : 0 ≤ lam f := by sorry
