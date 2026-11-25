-- Prove2me | Theorems.Thm_BeckFialaMatrix_exists_round_all_slack
-- name    : BeckFialaMatrix.exists_round_all_slack
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T11:00:15.492333+00:00
-- url     : https://prove2.me/theorems/80107c7b-1899-58f8-be69-42b81644a62f
-- title:
--   Beck Fiala Matrix: exists round all slack
-- statement:
--   If every row is slack, rounding all floating coordinates down already works.
--
--   Source: https://github.com/jtraverso/beck-fiala/blob/52f1a12a140b0589ac39619dfd07807d98fdbaf5/LeanPool/BeckFialaMatrix/Basic.lean#L297-L311
-- source:
--   https://github.com/jtraverso/beck-fiala/blob/52f1a12a140b0589ac39619dfd07807d98fdbaf5/LeanPool/BeckFialaMatrix/Basic.lean#L297-L311

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

theorem BeckFialaMatrix.exists_round_all_slack {t : ℕ} (ht : 1 ≤ t) (A : Fin m → Fin N → ℤ)
    (hA : ∀ j i, A j i = 0 ∨ A j i = 1) (x : Fin N → ℚ) (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hall : ∀ j, floatingDegree A x j ≤ t) :
    ∃ y : Fin N → ℤ, (∀ i, y i = 0 ∨ y i = 1) ∧
      (∀ i ∉ floatingCoordinates x, (y i : ℚ) = x i) ∧
      ∀ j, |∑ i, (A j i : ℚ) * ((y i : ℚ) - x i)| < (t : ℚ) := by sorry
