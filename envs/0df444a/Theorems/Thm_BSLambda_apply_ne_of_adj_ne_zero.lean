-- Prove2me | Theorems.Thm_BSLambda_apply_ne_of_adj_ne_zero
-- name    : BSLambda.apply_ne_of_adj_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:02:24.220855+00:00
-- url     : https://prove2.me/theorems/e876cd9e-3b92-4315-a546-7a33853acc1f
-- title:
--   BSLambda: apply ne of adj ne zero
-- statement:
--   Adjacent inputs take different `f`-values.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Spectral.lean#L57-L59
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Spectral.lean#L57-L59

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

theorem BSLambda.apply_ne_of_adj_ne_zero (f : Input V → Bool) {x y : Input V} (h : adj f x y ≠ 0) :
    f x ≠ f y := by sorry
