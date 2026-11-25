-- Prove2me | Theorems.Thm_BeckFialaMatrix_eq_zero_or_one_of_not_floating
-- name    : BeckFialaMatrix.eq_zero_or_one_of_not_floating
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:55:40.21184+00:00
-- url     : https://prove2.me/theorems/389d63c2-0675-4091-9a6c-6b3a3162d054
-- title:
--   Beck Fiala Matrix: eq zero or one of not floating
-- statement:
--   A coordinate that is not floating and lies in `[0,1]` is `0` or `1`.
--
--   Source: https://github.com/jtraverso/beck-fiala/blob/52f1a12a140b0589ac39619dfd07807d98fdbaf5/LeanPool/BeckFialaMatrix/Basic.lean#L55-L61
-- source:
--   https://github.com/jtraverso/beck-fiala/blob/52f1a12a140b0589ac39619dfd07807d98fdbaf5/LeanPool/BeckFialaMatrix/Basic.lean#L55-L61

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

theorem BeckFialaMatrix.eq_zero_or_one_of_not_floating {x : Fin N → ℚ} {i : Fin N}
    (hx : 0 ≤ x i ∧ x i ≤ 1) (h : i ∉ floatingCoordinates x) : x i = 0 ∨ x i = 1 := by sorry
