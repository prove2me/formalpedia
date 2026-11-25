-- Prove2me | Theorems.Thm_BeckFialaMatrix_exists_rounding_step
-- name    : BeckFialaMatrix.exists_rounding_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T11:00:09.417556+00:00
-- url     : https://prove2.me/theorems/81d937aa-e300-527f-a08c-4c6ed1aec750
-- title:
--   Beck Fiala Matrix: exists rounding step
-- statement:
--   One rounding step: if some row is tight, we can strictly decrease the number of floating
--   coordinates while keeping the frozen coordinates and all tight-row sums fixed.
--
--   Source: https://github.com/jtraverso/beck-fiala/blob/52f1a12a140b0589ac39619dfd07807d98fdbaf5/LeanPool/BeckFialaMatrix/Basic.lean#L252-L294
-- source:
--   https://github.com/jtraverso/beck-fiala/blob/52f1a12a140b0589ac39619dfd07807d98fdbaf5/LeanPool/BeckFialaMatrix/Basic.lean#L252-L294

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

theorem BeckFialaMatrix.exists_rounding_step {t : ℕ} (A : Fin m → Fin N → ℤ)
    (hdeg : ∀ i, (univ.filter (fun j => A j i = 1)).card ≤ t)
    (x : Fin N → ℚ) (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (j0 : Fin m) (hj0 : t < floatingDegree A x j0) :
    ∃ x' : Fin N → ℚ, (∀ i, 0 ≤ x' i ∧ x' i ≤ 1) ∧
      (∀ i ∉ floatingCoordinates x, x' i = x i) ∧
      (floatingCoordinates x').card < (floatingCoordinates x).card ∧
      (∀ j, t < floatingDegree A x j → ∑ i, (A j i : ℚ) * x' i = ∑ i, (A j i : ℚ) * x i) := by sorry
