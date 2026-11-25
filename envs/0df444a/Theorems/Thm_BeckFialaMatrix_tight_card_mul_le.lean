-- Prove2me | Theorems.Thm_BeckFialaMatrix_tight_card_mul_le
-- name    : BeckFialaMatrix.tight_card_mul_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:55:48.186405+00:00
-- url     : https://prove2.me/theorems/96ea778f-06c9-43b0-a2bd-bb2f247aa416
-- title:
--   Beck Fiala Matrix: tight card mul le
-- statement:
--   Double counting: `(t+1) * #tight ≤ t * #floating`.
--
--   Source: https://github.com/jtraverso/beck-fiala/blob/52f1a12a140b0589ac39619dfd07807d98fdbaf5/LeanPool/BeckFialaMatrix/Basic.lean#L109-L133
-- source:
--   https://github.com/jtraverso/beck-fiala/blob/52f1a12a140b0589ac39619dfd07807d98fdbaf5/LeanPool/BeckFialaMatrix/Basic.lean#L109-L133

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

theorem BeckFialaMatrix.tight_card_mul_le {t : ℕ} (A : Fin m → Fin N → ℤ)
    (hdeg : ∀ i, (univ.filter (fun j => A j i = 1)).card ≤ t) (x : Fin N → ℚ) :
    (univ.filter (fun j => t < floatingDegree A x j)).card * (t + 1) ≤
      (floatingCoordinates x).card * t := by sorry
