-- Prove2me | Theorems.Thm_BinaryMatrix_transpose_shatters_imp_shatters
-- name    : BinaryMatrix.transpose_shatters_imp_shatters
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:31:42.68312+00:00
-- url     : https://prove2.me/theorems/3d0dd33d-4301-4d44-9e6e-b52aa8fed061
-- title:
--   Binary Matrix: transpose shatters imp shatters
-- statement:
--   Auxiliary: if `M.transpose` shatters `S ⊆ Fin m` with `|S| ≥ 2^(d+1)`,
--       then `M` shatters some set of `d+1` columns.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/PureMath/BinaryMatrix.lean#L126-L206
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/PureMath/BinaryMatrix.lean#L126-L206

module
public import Mathlib.Combinatorics.SetFamily.Shatter
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_BinaryMatrix
set_option autoImplicit true
@[expose] public section
public section
open Finset
universe u
open BinaryMatrix

theorem BinaryMatrix.transpose_shatters_imp_shatters {m n : ℕ} (M : BinaryMatrix m n)
    {d : ℕ} (S : Finset (Fin m)) (hS : M.transpose.shatters S)
    (hcard : 2 ^ (d + 1) ≤ S.card) :
    ∃ T : Finset (Fin n), T.card = d + 1 ∧ M.shatters T := by sorry
