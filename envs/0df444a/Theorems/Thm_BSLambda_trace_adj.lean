-- Prove2me | Theorems.Thm_BSLambda_trace_adj
-- name    : BSLambda.trace_adj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:04:58.286293+00:00
-- url     : https://prove2.me/theorems/5754b68a-644b-44f3-9152-c2bf8e3916e2
-- title:
--   BSLambda: trace adj
-- statement:
--   The trace of the sensitivity adjacency matrix vanishes: no input is its own neighbour.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Spectral.lean#L115-L117
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Spectral.lean#L115-L117

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

theorem BSLambda.trace_adj (f : Input V → Bool) : (adj f).trace = 0 := by sorry
