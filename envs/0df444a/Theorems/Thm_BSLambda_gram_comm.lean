-- Prove2me | Theorems.Thm_BSLambda_gram_comm
-- name    : BSLambda.gram_comm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:05:00.324824+00:00
-- url     : https://prove2.me/theorems/7543950c-bf10-4349-9ccc-9857703b8ad8
-- title:
--   BSLambda: gram comm
-- statement:
--   The Gram matrix of Section 11.1 is symmetric, entrywise.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Bipartite.lean#L115-L117
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Bipartite.lean#L115-L117

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

theorem BSLambda.gram_comm {f : Input V → Bool} (x y : Ones f) : gram f x y = gram f y x := by sorry
