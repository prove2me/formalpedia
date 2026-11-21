-- Prove2me | Theorems.Thm_Corless_Dv_sub_eq
-- name    : Corless.Dv_sub_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:40:48.339184+00:00
-- url     : https://prove2.me/theorems/fac0fb1c-9343-405f-a6ca-6bae25aea8d4
-- title:
--   Corless: Dv sub eq
-- statement:
--   Exact telescoping over the edges of a path with `M` vertices.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CorlessNilpotent/Main.lean#L48-L59
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CorlessNilpotent/Main.lean#L48-L59

module
public import Mathlib.Algebra.BigOperators.Intervals
public import Definitions.Def_LeanPool_CorlessNilpotent_Parity
public import Definitions.Def_LeanPool_CorlessNilpotent_Main
set_option autoImplicit true
@[expose] public section
public section
open Polynomial Finset
open Corless

theorem Corless.Dv_sub_eq (s t : ℕ → ℤ) (M : ℕ) :
    Dv s M - Dv t M = ∑ j ∈ range (M - 1),
      C (s j - t j) * X * Dv (hyb s t j) j * Dv (fun i => hyb s t j (i + j + 2)) (M - 2 - j) := by sorry
