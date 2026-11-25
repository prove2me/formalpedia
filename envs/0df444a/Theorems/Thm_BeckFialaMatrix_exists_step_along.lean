-- Prove2me | Theorems.Thm_BeckFialaMatrix_exists_step_along
-- name    : BeckFialaMatrix.exists_step_along
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:55:51.723719+00:00
-- url     : https://prove2.me/theorems/f0acae57-53d8-41cd-8185-413cebde552b
-- title:
--   Beck Fiala Matrix: exists step along
-- statement:
--   Walking along a direction `v` supported on the floating set until a coordinate hits
--   `0` or `1`.
--
--   Source: https://github.com/jtraverso/beck-fiala/blob/52f1a12a140b0589ac39619dfd07807d98fdbaf5/LeanPool/BeckFialaMatrix/Basic.lean#L193-L248
-- source:
--   https://github.com/jtraverso/beck-fiala/blob/52f1a12a140b0589ac39619dfd07807d98fdbaf5/LeanPool/BeckFialaMatrix/Basic.lean#L193-L248

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

theorem BeckFialaMatrix.exists_step_along (x : Fin N → ℚ) (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (F : Finset (Fin N)) (hF : ∀ i ∈ F, 0 < x i ∧ x i < 1)
    (v : Fin N → ℚ) (hv0 : ∀ i ∉ F, v i = 0) (i0 : Fin N) (hi0 : i0 ∈ F) (hvi0 : v i0 ≠ 0) :
    ∃ s : ℚ, 0 < s ∧ (∀ i, 0 ≤ x i + s * v i ∧ x i + s * v i ≤ 1) ∧
      ∃ i ∈ F, x i + s * v i = 0 ∨ x i + s * v i = 1 := by sorry
