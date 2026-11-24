-- Prove2me | Theorems.Thm_BSLambda_adj_nonneg
-- name    : BSLambda.adj_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:02:12.963772+00:00
-- url     : https://prove2.me/theorems/a7801f3c-4571-4dff-8395-45e10724aa3a
-- title:
--   BSLambda: adj nonneg
-- statement:
--   The sensitivity adjacency matrix has nonnegative entries.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Spectral.lean#L43-L45
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Spectral.lean#L43-L45

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

theorem BSLambda.adj_nonneg (f : Input V → Bool) (x y : Input V) : 0 ≤ adj f x y := by sorry
