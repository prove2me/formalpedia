-- Prove2me | Theorems.Thm_Corless_charmatrix_T
-- name    : Corless.charmatrix_T
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:41:54.274438+00:00
-- url     : https://prove2.me/theorems/ddea4056-5937-4fd1-bd78-5d4e179ef45e
-- title:
--   Corless: charmatrix T
-- statement:
--   The Corless construction uses the charmatrix T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CorlessNilpotent/Matrix.lean#L35-L35
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CorlessNilpotent/Matrix.lean#L35-L35

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

theorem Corless.charmatrix_T (m : ℕ) (u : ℕ → ℂ) : charmatrix (T m u) = CM m u := by sorry
