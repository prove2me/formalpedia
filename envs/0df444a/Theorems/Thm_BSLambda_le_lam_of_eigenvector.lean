-- Prove2me | Theorems.Thm_BSLambda_le_lam_of_eigenvector
-- name    : BSLambda.le_lam_of_eigenvector
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:59:14.732848+00:00
-- url     : https://prove2.me/theorems/df271d0e-6bf3-4c7a-8122-08f739cd1c14
-- title:
--   BSLambda: le lam of eigenvector
-- statement:
--   An eigenvalue of `A_f` is at most `lambda(f)`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/OpNorm.lean#L38-L40
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/OpNorm.lean#L38-L40

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Bipartite
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_OpNorm
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open scoped Matrix Matrix.Norms.L2Operator
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BSLambda.le_lam_of_eigenvector (f : Input V → Bool) {μ : ℝ} {v : Input V → ℝ} (hv : v ≠ 0)
    (hev : adj f *ᵥ v = μ • v) : μ ≤ lam f := by sorry
