-- Prove2me | Theorems.Thm_BSLambda_adj_apply_eq_one_iff
-- name    : BSLambda.adj_apply_eq_one_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:04:29.873201+00:00
-- url     : https://prove2.me/theorems/1454dcbd-e149-4f39-b699-6de2bff6c3cc
-- title:
--   BSLambda: adj apply eq one iff
-- statement:
--   The BSLambda construction uses the adj apply eq one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Spectral.lean#L47-L49
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Spectral.lean#L47-L49

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

theorem BSLambda.adj_apply_eq_one_iff {f : Input V → Bool} {x y : Input V} :
    adj f x y = 1 ↔ hammingDist x y = 1 ∧ f x ≠ f y := by sorry
