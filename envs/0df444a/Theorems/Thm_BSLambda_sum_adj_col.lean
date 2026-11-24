-- Prove2me | Theorems.Thm_BSLambda_sum_adj_col
-- name    : BSLambda.sum_adj_col
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:04:49.638801+00:00
-- url     : https://prove2.me/theorems/5c57d112-8589-4733-9fad-d99030f84927
-- title:
--   BSLambda: sum adj col
-- statement:
--   Column sums of the sensitivity adjacency matrix: it is symmetric (`adj_comm`), so they
--   agree with the row sums of `sum_adj_row`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Spectral.lean#L111-L112
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Spectral.lean#L111-L112

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

theorem BSLambda.sum_adj_col (f : Input V → Bool) (y : Input V) : ∑ x, adj f x y = (sensAt f y : ℝ) := by sorry
