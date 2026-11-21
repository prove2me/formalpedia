-- Prove2me | Theorems.Thm_Corless_reflect_E_eq_iff
-- name    : Corless.reflect_E_eq_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:41:50.856339+00:00
-- url     : https://prove2.me/theorems/d6b10db3-0099-430b-991a-f1768383fdce
-- title:
--   Corless: reflect E eq iff
-- statement:
--   `reflect m (E s m) = X ^ m` iff `Dv s m = 1`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CorlessNilpotent/Matrix.lean#L184-L198
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CorlessNilpotent/Matrix.lean#L184-L198

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

theorem Corless.reflect_E_eq_iff (s : ℕ → ℤ) (m : ℕ) : reflect m (E s m) = X ^ m ↔ Dv s m = 1 := by sorry
