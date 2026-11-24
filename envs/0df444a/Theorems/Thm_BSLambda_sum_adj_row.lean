-- Prove2me | Theorems.Thm_BSLambda_sum_adj_row
-- name    : BSLambda.sum_adj_row
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:58:13.943043+00:00
-- url     : https://prove2.me/theorems/677a3947-905f-48ad-a1f5-6cb87743b585
-- title:
--   BSLambda: sum adj row
-- statement:
--   Every row of `adj f` sums to the sensitivity at that point.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Spectral.lean#L105-L107
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Spectral.lean#L105-L107

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

theorem BSLambda.sum_adj_row (f : Input V → Bool) (x : Input V) :
    ∑ y, adj f x y = (sensAt f x : ℝ) := by sorry
