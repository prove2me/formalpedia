-- Prove2me | Theorems.Thm_BSLambda_mem_nbrs
-- name    : BSLambda.mem_nbrs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:58:55.604996+00:00
-- url     : https://prove2.me/theorems/499446d0-5ace-4dc6-ab88-64876f73aebb
-- title:
--   BSLambda: mem nbrs
-- statement:
--   `y` is a neighbour of `x` exactly when they are Hamming neighbours separated by `f`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Spectral.lean#L79-L81
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Spectral.lean#L79-L81

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

theorem BSLambda.mem_nbrs {f : Input V → Bool} {x y : Input V} :
    y ∈ nbrs f x ↔ hammingDist x y = 1 ∧ f x ≠ f y := by sorry
