-- Prove2me | Theorems.Thm_BinaryMatrix_bool_fun_eq_of_filter_eq
-- name    : BinaryMatrix.bool_fun_eq_of_filter_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:31:44.911075+00:00
-- url     : https://prove2.me/theorems/91472a8c-cf93-4b8a-91ca-0a2a588a4621
-- title:
--   Binary Matrix: bool fun eq of filter eq
-- statement:
--   Two `Bool`-valued functions on `Fin n` that agree on which indices are `true`
--       (as witnessed by equal `univ.filter`) are equal.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/PureMath/BinaryMatrix.lean#L84-L97
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/PureMath/BinaryMatrix.lean#L84-L97

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

theorem BinaryMatrix.bool_fun_eq_of_filter_eq {n : ℕ} (f g : Fin n → Bool)
    (h : Finset.univ.filter (fun j => f j = true) =
         Finset.univ.filter (fun j => g j = true)) :
    f = g := by sorry
