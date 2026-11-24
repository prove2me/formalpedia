-- Prove2me | Theorems.Thm_BSLambda_mulVec_adj_ones
-- name    : BSLambda.mulVec_adj_ones
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:05:09.954844+00:00
-- url     : https://prove2.me/theorems/bd21ac19-f947-4ab6-be43-1bf2e5b655ff
-- title:
--   BSLambda: mul Vec adj ones
-- statement:
--   The `Ones f` rows of the block decomposition of `A_f`: at a positive input, `A_f *ᵥ v` sees
--   only the negative coordinates of `v`, and there it is governed by `M` (Section 11.1).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Bipartite.lean#L148-L154
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Bipartite.lean#L148-L154

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

theorem BSLambda.mulVec_adj_ones (f : Input V → Bool) (v : Input V → ℝ) (x : Ones f) :
    (adj f *ᵥ v) x.1 = (biadj f *ᵥ fun z : Zeros f ↦ v z.1) x := by sorry
