-- Prove2me | Theorems.Thm_BSLambda_sum_ones_add_sum_zeros
-- name    : BSLambda.sum_ones_add_sum_zeros
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:59:13.956995+00:00
-- url     : https://prove2.me/theorems/64ba7788-7803-44c7-9a6e-2908e7b865ac
-- title:
--   BSLambda: sum ones add sum zeros
-- statement:
--   Splitting a sum over all inputs into its positive and its negative part (Section 11.1).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Bipartite.lean#L88-L93
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Bipartite.lean#L88-L93

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Spectral
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_SchurTest
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Bipartite
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open scoped Matrix Matrix.Norms.L2Operator
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BSLambda.sum_ones_add_sum_zeros (f : Input V → Bool) (g : Input V → ℝ) :
    ∑ x : Ones f, g x.1 + ∑ z : Zeros f, g z.1 = ∑ y : Input V, g y := by sorry
