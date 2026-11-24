-- Prove2me | Theorems.Thm_BSLambda_biadj_apply
-- name    : BSLambda.biadj_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:58:52.150166+00:00
-- url     : https://prove2.me/theorems/b1671ec1-c99d-4240-9551-4004541f3587
-- title:
--   BSLambda: biadj apply
-- statement:
--   Entries of the biadjacency matrix of Section 11.1.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Bipartite.lean#L63-L64
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Bipartite.lean#L63-L64

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

theorem BSLambda.biadj_apply (f : Input V → Bool) (x : Ones f) (z : Zeros f) :
    biadj f x z = if hammingDist x.1 z.1 = 1 then (1 : ℝ) else 0 := by sorry
