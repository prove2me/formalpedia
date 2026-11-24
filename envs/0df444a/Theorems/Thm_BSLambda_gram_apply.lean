-- Prove2me | Theorems.Thm_BSLambda_gram_apply
-- name    : BSLambda.gram_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:58:26.631551+00:00
-- url     : https://prove2.me/theorems/2a03921e-feee-43b4-8574-df1af8b1958c
-- title:
--   BSLambda: gram apply
-- statement:
--   **Counting form of the Gram entries.**  For `x, y ∈ S`, the entry `K_{x,y}` counts the
--   negative inputs adjacent to both `x` and `y` (Section 11.1 of `bs_lambda.txt`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Bipartite.lean#L99-L104
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Bipartite.lean#L99-L104

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

theorem BSLambda.gram_apply (f : Input V → Bool) (x y : Ones f) :
    gram f x y =
      ((Finset.univ.filter fun z : Zeros f =>
          hammingDist x.1 z.1 = 1 ∧ hammingDist y.1 z.1 = 1).card : ℝ) := by sorry
