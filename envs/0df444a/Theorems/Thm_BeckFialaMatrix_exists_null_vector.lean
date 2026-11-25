-- Prove2me | Theorems.Thm_BeckFialaMatrix_exists_null_vector
-- name    : BeckFialaMatrix.exists_null_vector
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:55:54.88803+00:00
-- url     : https://prove2.me/theorems/e1645687-c5ad-4cd8-b449-e3fb511d12ab
-- title:
--   Beck Fiala Matrix: exists null vector
-- statement:
--   An underdetermined homogeneous system has a nonzero solution supported on `F`.
--
--   Source: https://github.com/jtraverso/beck-fiala/blob/52f1a12a140b0589ac39619dfd07807d98fdbaf5/LeanPool/BeckFialaMatrix/Basic.lean#L149-L189
-- source:
--   https://github.com/jtraverso/beck-fiala/blob/52f1a12a140b0589ac39619dfd07807d98fdbaf5/LeanPool/BeckFialaMatrix/Basic.lean#L149-L189

module
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring
public import Definitions.Def_LeanPool_BeckFialaMatrix_Basic
set_option autoImplicit true
@[expose] public section
public section
open Finset
open BeckFialaMatrix
variable {m N : ℕ}

theorem BeckFialaMatrix.exists_null_vector (A : Fin m → Fin N → ℤ) (F : Finset (Fin N)) (T : Finset (Fin m))
    (hcard : T.card < F.card) :
    ∃ v : Fin N → ℚ, (∀ i ∉ F, v i = 0) ∧ (∃ i ∈ F, v i ≠ 0) ∧
      ∀ j ∈ T, ∑ i, (A j i : ℚ) * v i = 0 := by sorry
