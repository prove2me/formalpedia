-- Prove2me | Theorems.Thm_BeckFialaMatrix_exists_rounding
-- name    : BeckFialaMatrix.exists_rounding
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:55:37.146909+00:00
-- url     : https://prove2.me/theorems/35b23264-53ad-435e-8c4c-87978d83dec3
-- title:
--   Beck Fiala Matrix: exists rounding
-- statement:
--   **Beck–Fiala integer-making theorem.**  If every element lies in at most `t` sets of a
--   set system (i.e. every column of the 0/1 incidence matrix `A` has at most `t` ones) and
--   `x ∈ [0,1]^N` is fractional, then `x` can be rounded to an integral `y ∈ {0,1}^N` whose
--   discrepancy on every row is `< t`.
--
--   (The extra hypothesis `1 ≤ t` is necessary; see `zero_bound_counterexample` below.)
--
--   Source: https://github.com/jtraverso/beck-fiala/blob/52f1a12a140b0589ac39619dfd07807d98fdbaf5/LeanPool/BeckFialaMatrix/Basic.lean#L380-L388
-- source:
--   https://github.com/jtraverso/beck-fiala/blob/52f1a12a140b0589ac39619dfd07807d98fdbaf5/LeanPool/BeckFialaMatrix/Basic.lean#L380-L388

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

theorem BeckFialaMatrix.exists_rounding {m N t : ℕ} (ht : 1 ≤ t)
    (A : Fin m → Fin N → ℤ)
    (hA : ∀ j i, A j i = 0 ∨ A j i = 1)
    (hdeg : ∀ i, (Finset.univ.filter (fun j => A j i = 1)).card ≤ t)
    (x : Fin N → ℚ) (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) :
    ∃ y : Fin N → ℤ, (∀ i, y i = 0 ∨ y i = 1) ∧
      ∀ j, |∑ i, (A j i : ℚ) * ((y i : ℚ) - x i)| < (t : ℚ) := by sorry
