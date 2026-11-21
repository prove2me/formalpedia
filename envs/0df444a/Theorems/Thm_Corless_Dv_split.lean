-- Prove2me | Theorems.Thm_Corless_Dv_split
-- name    : Corless.Dv_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:39:56.543812+00:00
-- url     : https://prove2.me/theorems/ee5a65c3-ed7a-4218-bee2-865c45bc7d4c
-- title:
--   Corless: Dv split
-- statement:
--   Splitting the path at the edge `k` (between the vertices `k` and `k + 1`): matchings either
--   avoid the edge (left part times right part) or use it.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CorlessNilpotent/Path.lean#L52-L71
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CorlessNilpotent/Path.lean#L52-L71

module
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Tactic.Ring
public import Definitions.Def_LeanPool_CorlessNilpotent_Path
set_option autoImplicit true
@[expose] public section
public section
open Polynomial Finset
open Corless

theorem Corless.Dv_split (s : ℕ → ℤ) (k : ℕ) : ∀ m : ℕ,
    Dv s (k + m + 2) = Dv s (k + 1) * Dv (fun i => s (i + k + 1)) (m + 1)
      + C (s k) * X * Dv s k * Dv (fun i => s (i + k + 2)) m
  := by sorry
