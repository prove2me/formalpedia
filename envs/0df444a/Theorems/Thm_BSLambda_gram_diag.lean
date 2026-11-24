-- Prove2me | Theorems.Thm_BSLambda_gram_diag
-- name    : BSLambda.gram_diag
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:04:58.397858+00:00
-- url     : https://prove2.me/theorems/ea96dc03-a2f2-4956-b612-096cd7c552a1
-- title:
--   BSLambda: gram diag
-- statement:
--   On the diagonal, `K_{x,x} = s(f,x)` (Section 11.1 of `bs_lambda.txt`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Bipartite.lean#L125-L137
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Bipartite.lean#L125-L137

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

theorem BSLambda.gram_diag (f : Input V → Bool) (x : Ones f) : gram f x x = (sensAt f x.1 : ℝ) := by sorry
