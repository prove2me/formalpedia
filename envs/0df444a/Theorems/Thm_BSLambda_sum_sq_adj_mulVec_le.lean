-- Prove2me | Theorems.Thm_BSLambda_sum_sq_adj_mulVec_le
-- name    : BSLambda.sum_sq_adj_mulVec_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:04:12.362342+00:00
-- url     : https://prove2.me/theorems/5fc81e7d-dddf-447a-849c-bdc470544c17
-- title:
--   BSLambda: sum sq adj mul Vec le
-- statement:
--   The operator bound defining `lambda(f)`, in sum-of-squares form.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/OpNorm.lean#L109-L111
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/OpNorm.lean#L109-L111

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Bipartite
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_OpNorm
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open scoped Matrix Matrix.Norms.L2Operator
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BSLambda.sum_sq_adj_mulVec_le (f : Input V → Bool) (v : Input V → ℝ) :
    ∑ x, (adj f *ᵥ v) x ^ 2 ≤ lam f ^ 2 * ∑ x, v x ^ 2 := by sorry
