-- Prove2me | Theorems.Thm_AME125_CutInj_submatrix
-- name    : AME125.CutInj.submatrix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:03:28.206976+00:00
-- url     : https://prove2.me/theorems/72b2f8b3-4c4e-5d16-8cc1-c58d1257341e
-- title:
--   Cut Inj: submatrix
-- statement:
--   Permuting the matrix moves the cut: the cut condition for `A` and the permuted matrix
--   follows from the cut condition for the image of `A`.
--
--   Source: https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/GraphState.lean#L142-L155
-- source:
--   https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/GraphState.lean#L142-L155

module
public import Definitions.Def_AME125_Defs
public import Definitions.Def_AME125_GraphState
set_option autoImplicit false
@[expose] public section
public section
open AME125
open OpenQuantumProblem35
open scoped Matrix

theorem AME125.CutInj.submatrix {n : ℕ} {S : Matrix (Fin n) (Fin n) (ZMod 5)} (π : Equiv.Perm (Fin n))
    {A : Finset (Fin n)} (h : CutInj S (A.map π.symm.toEmbedding)) :
    CutInj (S.submatrix π.symm π.symm) A := by sorry
