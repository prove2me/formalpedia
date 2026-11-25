-- Prove2me | Theorems.Thm_BeckFialaMatrix_zero_bound_counterexample
-- name    : BeckFialaMatrix.zero_bound_counterexample
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T11:00:41.792466+00:00
-- url     : https://prove2.me/theorems/0205f6e4-987d-435d-8a20-c92f7e8269ff
-- title:
--   Beck Fiala Matrix: zero bound counterexample
-- statement:
--   The hypothesis `1 ≤ t` cannot be dropped: for `t = 0` the conclusion would read
--   `|0| < 0`.
--
--   Source: https://github.com/jtraverso/beck-fiala/blob/52f1a12a140b0589ac39619dfd07807d98fdbaf5/LeanPool/BeckFialaMatrix/Basic.lean#L392-L402
-- source:
--   https://github.com/jtraverso/beck-fiala/blob/52f1a12a140b0589ac39619dfd07807d98fdbaf5/LeanPool/BeckFialaMatrix/Basic.lean#L392-L402

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

theorem BeckFialaMatrix.zero_bound_counterexample :
    ¬ (∀ (m N t : ℕ) (A : Fin m → Fin N → ℤ), (∀ j i, A j i = 0 ∨ A j i = 1) →
        (∀ i, (Finset.univ.filter (fun j => A j i = 1)).card ≤ t) →
        ∀ x : Fin N → ℚ, (∀ i, 0 ≤ x i ∧ x i ≤ 1) →
        ∃ y : Fin N → ℤ, (∀ i, y i = 0 ∨ y i = 1) ∧
          ∀ j, |∑ i, (A j i : ℚ) * ((y i : ℚ) - x i)| < (t : ℚ)) := by sorry
