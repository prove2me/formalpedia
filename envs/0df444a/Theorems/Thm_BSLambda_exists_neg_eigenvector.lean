-- Prove2me | Theorems.Thm_BSLambda_exists_neg_eigenvector
-- name    : BSLambda.exists_neg_eigenvector
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:09:28.191387+00:00
-- url     : https://prove2.me/theorems/c85584fa-442f-4ee6-8aba-b782d3a467fe
-- title:
--   BSLambda: exists neg eigenvector
-- statement:
--   The sign flip `x ↦ (-1)^{f x}` conjugates an eigenvector for `μ` into one for `-μ`: every
--   edge of the sensitivity graph joins inputs with different `f`-values.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/OpNorm.lean#L67-L84
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/OpNorm.lean#L67-L84

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Bipartite
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_OpNorm
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open scoped Matrix Matrix.Norms.L2Operator
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BSLambda.exists_neg_eigenvector (f : Input V → Bool) {μ : ℝ} {v : Input V → ℝ} (hv : v ≠ 0)
    (hev : adj f *ᵥ v = μ • v) : ∃ w : Input V → ℝ, w ≠ 0 ∧ adj f *ᵥ w = (-μ) • w := by sorry
