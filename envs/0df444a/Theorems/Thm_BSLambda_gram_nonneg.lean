-- Prove2me | Theorems.Thm_BSLambda_gram_nonneg
-- name    : BSLambda.gram_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:02:51.417623+00:00
-- url     : https://prove2.me/theorems/d34af176-8803-4e9f-b8d9-a8a4b35cf5f5
-- title:
--   BSLambda: gram nonneg
-- statement:
--   The Gram matrix of Section 11.1 has nonnegative entries.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Bipartite.lean#L120-L122
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Bipartite.lean#L120-L122

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

theorem BSLambda.gram_nonneg (f : Input V → Bool) (x y : Ones f) : 0 ≤ gram f x y := by sorry
