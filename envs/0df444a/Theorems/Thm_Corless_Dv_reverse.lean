-- Prove2me | Theorems.Thm_Corless_Dv_reverse
-- name    : Corless.Dv_reverse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:39:57.458614+00:00
-- url     : https://prove2.me/theorems/0156ab5f-151f-46ef-9c17-7177ea6e66a8
-- title:
--   Corless: Dv reverse
-- statement:
--   Reversing the path does not change its matching polynomial.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CorlessNilpotent/Path.lean#L81-L99
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CorlessNilpotent/Path.lean#L81-L99

module
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Tactic.Ring
public import Definitions.Def_LeanPool_CorlessNilpotent_Path
set_option autoImplicit true
@[expose] public section
public section
open Polynomial Finset
open Corless

theorem Corless.Dv_reverse (s : ℕ → ℤ) : ∀ j : ℕ, Dv (fun i => s (j - 2 - i)) j = Dv s j
  := by sorry
