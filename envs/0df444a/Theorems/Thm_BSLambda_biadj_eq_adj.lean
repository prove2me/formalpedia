-- Prove2me | Theorems.Thm_BSLambda_biadj_eq_adj
-- name    : BSLambda.biadj_eq_adj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:02:32.5604+00:00
-- url     : https://prove2.me/theorems/d4d4c13e-41c0-4a02-9725-139363549ccd
-- title:
--   BSLambda: biadj eq adj
-- statement:
--   The biadjacency matrix is the restriction of the adjacency matrix to `S × T`: the
--   condition `f x ≠ f z` of `BSLambda.adj` is automatic there (Section 11.1).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Bipartite.lean#L75-L78
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Bipartite.lean#L75-L78

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

theorem BSLambda.biadj_eq_adj (f : Input V → Bool) (x : Ones f) (z : Zeros f) :
    biadj f x z = adj f x.1 z.1 := by sorry
