-- Prove2me | Theorems.Thm_Corless_isNilpotent_iff_charpoly_matrix
-- name    : Corless.isNilpotent_iff_charpoly_matrix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:41:51.246197+00:00
-- url     : https://prove2.me/theorems/be9e9d43-ca16-4422-9aca-2b3698ecbce8
-- title:
--   Corless: is Nilpotent iff charpoly matrix
-- statement:
--   A complex square matrix is nilpotent iff its characteristic polynomial is `X ^ size`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CorlessNilpotent/Matrix.lean#L173-L181
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CorlessNilpotent/Matrix.lean#L173-L181

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

theorem Corless.isNilpotent_iff_charpoly_matrix {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) :
    IsNilpotent A ↔ A.charpoly = X ^ m := by sorry
