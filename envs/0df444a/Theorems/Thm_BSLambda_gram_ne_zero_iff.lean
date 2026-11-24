-- Prove2me | Theorems.Thm_BSLambda_gram_ne_zero_iff
-- name    : BSLambda.gram_ne_zero_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:02:41.583803+00:00
-- url     : https://prove2.me/theorems/88fd5b26-e91a-46b6-bce8-0ce66255b1ef
-- title:
--   BSLambda: gram ne zero iff
-- statement:
--   A Gram entry is nonzero exactly when the two positive inputs have a common negative
--   Hamming neighbour: `gram_apply` with the cardinality turned into an existential
--   (Section 11.1).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Bipartite.lean#L109-L112
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Bipartite.lean#L109-L112

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

theorem BSLambda.gram_ne_zero_iff {f : Input V → Bool} {x y : Ones f} :
    gram f x y ≠ 0 ↔ ∃ z : Zeros f, hammingDist x.1 z.1 = 1 ∧ hammingDist y.1 z.1 = 1 := by sorry
