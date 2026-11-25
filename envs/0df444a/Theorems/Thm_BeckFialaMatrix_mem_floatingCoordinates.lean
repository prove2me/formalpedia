-- Prove2me | Theorems.Thm_BeckFialaMatrix_mem_floatingCoordinates
-- name    : BeckFialaMatrix.mem_floatingCoordinates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:55:14.254903+00:00
-- url     : https://prove2.me/theorems/4d6e2978-19c3-488a-9c61-7959ce6be685
-- title:
--   Beck Fiala Matrix: mem floating Coordinates
-- statement:
--   The Beck Fiala Matrix construction uses the mem floating Coordinates property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/beck-fiala/blob/52f1a12a140b0589ac39619dfd07807d98fdbaf5/LeanPool/BeckFialaMatrix/Basic.lean#L50-L52
-- source:
--   https://github.com/jtraverso/beck-fiala/blob/52f1a12a140b0589ac39619dfd07807d98fdbaf5/LeanPool/BeckFialaMatrix/Basic.lean#L50-L52

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

theorem BeckFialaMatrix.mem_floatingCoordinates {x : Fin N → ℚ} {i : Fin N} :
    i ∈ floatingCoordinates x ↔ 0 < x i ∧ x i < 1 := by sorry
