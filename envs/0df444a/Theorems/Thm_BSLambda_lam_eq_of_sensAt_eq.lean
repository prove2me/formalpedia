-- Prove2me | Theorems.Thm_BSLambda_lam_eq_of_sensAt_eq
-- name    : BSLambda.lam_eq_of_sensAt_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:09:32.186286+00:00
-- url     : https://prove2.me/theorems/719b4f2c-8c0f-4493-8453-9d7eae01baae
-- title:
--   BSLambda: lam eq of sens At eq
-- statement:
--   A sensitivity graph all of whose vertices have degree `k` has `lambda = k`: the row sums
--   give `lam f ≤ k`, and the all-ones vector is an eigenvector for `k`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/OpNorm.lean#L161-L166
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/OpNorm.lean#L161-L166

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Bipartite
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_OpNorm
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open scoped Matrix Matrix.Norms.L2Operator
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BSLambda.lam_eq_of_sensAt_eq {f : Input V → Bool} {k : ℝ} (hk : 0 ≤ k)
    (hs : ∀ x, (sensAt f x : ℝ) = k) : lam f = k := by sorry
