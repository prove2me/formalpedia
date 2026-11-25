-- Prove2me | Theorems.Thm_BeckFiala_exists_rounding
-- name    : BeckFiala.exists_rounding
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T11:39:49.67585+00:00
-- url     : https://prove2.me/theorems/cdced0b4-9078-4bc7-b083-9ffb1e030435
-- title:
--   Beck Fiala: exists rounding
-- statement:
--   **Beck–Fiala integer-making theorem.** If every column of the `0/1` matrix `A` has at most
--   `t ≥ 1` ones and `x ∈ [0,1]^N`, then `x` can be rounded to `y ∈ {0,1}^N` with
--   `|∑ᵢ A j i (y i - x i)| < t` for every row `j`.
--
--   Source: https://github.com/jtraverso/beck-fiala/blob/52f1a12a140b0589ac39619dfd07807d98fdbaf5/Solution.lean#L28-L35
-- source:
--   https://github.com/jtraverso/beck-fiala/blob/52f1a12a140b0589ac39619dfd07807d98fdbaf5/Solution.lean#L28-L35

module
public import Mathlib
public import Definitions.Def_LeanPool_BeckFialaMatrix
public import Definitions.Def_BeckFiala_Solution
public import Theorems.Thm_BeckFialaMatrix_exists_rounding

set_option autoImplicit true
@[expose] public section
public section
open Finset
open BeckFiala

theorem BeckFiala.exists_rounding {m N t : ℕ} (ht : 1 ≤ t)
    (A : Fin m → Fin N → ℤ)
    (hA : ∀ j i, A j i = 0 ∨ A j i = 1)
    (hdeg : ∀ i, (Finset.univ.filter (fun j => A j i = 1)).card ≤ t)
    (x : Fin N → ℚ) (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) :
    ∃ y : Fin N → ℤ, (∀ i, y i = 0 ∨ y i = 1) ∧
      ∀ j, |∑ i, (A j i : ℚ) * ((y i : ℚ) - x i)| < (t : ℚ) := by sorry
