-- Prove2me | Theorems.Thm_BSLambda_sum_sq_adj_mulVec_side_le
-- name    : BSLambda.sum_sq_adj_mulVec_side_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:09:22.485226+00:00
-- url     : https://prove2.me/theorems/bf64be52-855c-413a-a7ca-2999ac8043b5
-- title:
--   BSLambda: sum sq adj mul Vec side le
-- statement:
--   The operator bound restricted to one side of the bipartition: `A_f *ᵥ v` reads `v` only on
--   the other side, so only the other side's coordinates appear on the right.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/OpNorm.lean#L115-L127
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/OpNorm.lean#L115-L127

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Bipartite
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_OpNorm
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open scoped Matrix Matrix.Norms.L2Operator
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BSLambda.sum_sq_adj_mulVec_side_le (f : Input V → Bool) (v : Input V → ℝ) (β : Bool) :
    ∑ x, (if f x = β then (adj f *ᵥ v) x else 0) ^ 2
      ≤ lam f ^ 2 * ∑ x, (if f x = β then 0 else v x) ^ 2 := by sorry
