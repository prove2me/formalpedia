-- Prove2me | Theorems.Thm_Corless_Dv_succ_succ_left
-- name    : Corless.Dv_succ_succ_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:39:56.322792+00:00
-- url     : https://prove2.me/theorems/541b91df-623a-4138-8a66-532f406ad597
-- title:
--   Corless: Dv succ succ left
-- statement:
--   The recurrence from the first vertex.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CorlessNilpotent/Path.lean#L74-L78
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CorlessNilpotent/Path.lean#L74-L78

module
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Tactic.Ring
public import Definitions.Def_LeanPool_CorlessNilpotent_Path
set_option autoImplicit true
@[expose] public section
public section
open Polynomial Finset
open Corless

theorem Corless.Dv_succ_succ_left (s : ℕ → ℤ) (m : ℕ) :
    Dv s (m + 2) = Dv (fun i => s (i + 1)) (m + 1) + C (s 0) * X * Dv (fun i => s (i + 2)) m := by sorry
