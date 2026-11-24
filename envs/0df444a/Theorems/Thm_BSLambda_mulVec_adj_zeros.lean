-- Prove2me | Theorems.Thm_BSLambda_mulVec_adj_zeros
-- name    : BSLambda.mulVec_adj_zeros
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:05:12.898988+00:00
-- url     : https://prove2.me/theorems/c51dd50c-5af2-467a-84a2-026e1328345e
-- title:
--   BSLambda: mul Vec adj zeros
-- statement:
--   The `Zeros f` rows of the block decomposition of `A_f`: at a negative input, `A_f *ᵥ v` sees
--   only the positive coordinates of `v`, and there it is governed by `Mᵀ` (Section 11.1).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Bipartite.lean#L158-L164
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Bipartite.lean#L158-L164

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

theorem BSLambda.mulVec_adj_zeros (f : Input V → Bool) (v : Input V → ℝ) (z : Zeros f) :
    (adj f *ᵥ v) z.1 = ((biadj f)ᵀ *ᵥ fun x : Ones f ↦ v x.1) z := by sorry
