-- Prove2me | Theorems.Thm_BeckFialaMatrix_tight_card_lt
-- name    : BeckFialaMatrix.tight_card_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:55:38.457715+00:00
-- url     : https://prove2.me/theorems/f2aeed4e-bd97-4c3c-8bbe-794bfc88c755
-- title:
--   Beck Fiala Matrix: tight card lt
-- statement:
--   The number of tight rows is strictly smaller than the number of floating variables.
--
--   Source: https://github.com/jtraverso/beck-fiala/blob/52f1a12a140b0589ac39619dfd07807d98fdbaf5/LeanPool/BeckFialaMatrix/Basic.lean#L136-L144
-- source:
--   https://github.com/jtraverso/beck-fiala/blob/52f1a12a140b0589ac39619dfd07807d98fdbaf5/LeanPool/BeckFialaMatrix/Basic.lean#L136-L144

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

theorem BeckFialaMatrix.tight_card_lt {t : ℕ} (A : Fin m → Fin N → ℤ)
    (hdeg : ∀ i, (univ.filter (fun j => A j i = 1)).card ≤ t) (x : Fin N → ℚ)
    (hne : (floatingCoordinates x).Nonempty) :
    (univ.filter (fun j => t < floatingDegree A x j)).card < (floatingCoordinates x).card := by sorry
