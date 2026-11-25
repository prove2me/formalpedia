-- Prove2me | Theorems.Thm_BeckFiala_exists_rounding_preserving_integral
-- name    : BeckFiala.exists_rounding_preserving_integral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T11:34:27.213445+00:00
-- url     : https://prove2.me/theorems/e7783269-ae51-4f94-92ec-c1c0bf35a8ab
-- title:
--   Beck Fiala: exists rounding preserving integral
-- statement:
--   **Beck–Fiala, strengthened.** The rounding can moreover be chosen to keep every coordinate of
--   `x` that is not strictly between `0` and `1`.
--
--   Source: https://github.com/jtraverso/beck-fiala/blob/52f1a12a140b0589ac39619dfd07807d98fdbaf5/Solution.lean#L39-L49
-- source:
--   https://github.com/jtraverso/beck-fiala/blob/52f1a12a140b0589ac39619dfd07807d98fdbaf5/Solution.lean#L39-L49

module
public import Mathlib
public import Definitions.Def_LeanPool_BeckFialaMatrix
public import Definitions.Def_BeckFiala_Solution
public import Theorems.Thm_BeckFialaMatrix_exists_rounding_preserving_integral

set_option autoImplicit true
@[expose] public section
public section
open Finset
open BeckFiala

theorem BeckFiala.exists_rounding_preserving_integral {m N t : ℕ} (ht : 1 ≤ t)
    (A : Fin m → Fin N → ℤ)
    (hA : ∀ j i, A j i = 0 ∨ A j i = 1)
    (hdeg : ∀ i, (Finset.univ.filter (fun j => A j i = 1)).card ≤ t)
    (x : Fin N → ℚ) (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) :
    ∃ y : Fin N → ℤ, (∀ i, y i = 0 ∨ y i = 1) ∧
      (∀ i, ¬ (0 < x i ∧ x i < 1) → (y i : ℚ) = x i) ∧
      ∀ j, |∑ i, (A j i : ℚ) * ((y i : ℚ) - x i)| < (t : ℚ) := by sorry
