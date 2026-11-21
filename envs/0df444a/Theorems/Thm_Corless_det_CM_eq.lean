-- Prove2me | Theorems.Thm_Corless_det_CM_eq
-- name    : Corless.det_CM_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:41:52.266676+00:00
-- url     : https://prove2.me/theorems/3c521b86-c43c-493a-8806-d5ed43e89cfa
-- title:
--   Corless: det CM eq
-- statement:
--   The characteristic polynomial of `T m u` is the reflection of `E s m`
--   when `s = u²` along the path edges.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CorlessNilpotent/Matrix.lean#L138-L170
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CorlessNilpotent/Matrix.lean#L138-L170

module
public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.Data.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Definitions.Def_LeanPool_CorlessNilpotent_Main
public import Definitions.Def_LeanPool_CorlessNilpotent_Matrix
set_option autoImplicit true
@[expose] public section
public section
open Polynomial Matrix
open Corless

theorem Corless.det_CM_eq : ∀ (m : ℕ) (s : ℕ → ℤ) (u : ℕ → ℂ),
    (∀ i, i + 1 < m → (s i : ℂ) = u i ^ 2) → (CM m u).det = reflect m (E s m)
  := by sorry
