-- Prove2me | Theorems.Thm_BeckFialaMatrix_slack_row_bound
-- name    : BeckFialaMatrix.slack_row_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:55:36.941356+00:00
-- url     : https://prove2.me/theorems/9c556908-f339-495a-803f-fe2d92f16b30
-- title:
--   Beck Fiala Matrix: slack row bound
-- statement:
--   If `y` is a `0/1` vector agreeing with `x` off the floating set, then on a row whose
--   floating degree is at most `t` (a *slack* row) the discrepancy is `< t`.
--
--   Source: https://github.com/jtraverso/beck-fiala/blob/52f1a12a140b0589ac39619dfd07807d98fdbaf5/LeanPool/BeckFialaMatrix/Basic.lean#L67-L104
-- source:
--   https://github.com/jtraverso/beck-fiala/blob/52f1a12a140b0589ac39619dfd07807d98fdbaf5/LeanPool/BeckFialaMatrix/Basic.lean#L67-L104

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

theorem BeckFialaMatrix.slack_row_bound {t : ℕ} (ht : 1 ≤ t) (A : Fin m → Fin N → ℤ)
    (hA : ∀ j i, A j i = 0 ∨ A j i = 1) (x : Fin N → ℚ)
    (y : Fin N → ℤ) (hy01 : ∀ i, y i = 0 ∨ y i = 1)
    (hagree : ∀ i ∉ floatingCoordinates x, (y i : ℚ) = x i) (j : Fin m)
    (hj : floatingDegree A x j ≤ t) :
    |∑ i, (A j i : ℚ) * ((y i : ℚ) - x i)| < (t : ℚ) := by sorry
