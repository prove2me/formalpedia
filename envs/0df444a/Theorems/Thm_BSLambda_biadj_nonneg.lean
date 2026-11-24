-- Prove2me | Theorems.Thm_BSLambda_biadj_nonneg
-- name    : BSLambda.biadj_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:10:25.00207+00:00
-- url     : https://prove2.me/theorems/f879546a-2658-4572-9466-cf6aa745aa34
-- title:
--   BSLambda: biadj nonneg
-- statement:
--   The biadjacency matrix of Section 11.1 has nonnegative entries.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Bipartite.lean#L68-L70
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Bipartite.lean#L68-L70

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
omit [DecidableEq V]

theorem BSLambda.biadj_nonneg (f : Input V → Bool) (x : Ones f) (z : Zeros f) : 0 ≤ biadj f x z := by sorry
