-- Prove2me | Theorems.Thm_Corless_CM_apply
-- name    : Corless.CM_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:41:46.846494+00:00
-- url     : https://prove2.me/theorems/79ee177c-48f6-4faa-bedb-450d41074f6f
-- title:
--   Corless: CM apply
-- statement:
--   The Corless construction uses the CM apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CorlessNilpotent/Matrix.lean#L37-L45
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CorlessNilpotent/Matrix.lean#L37-L45

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

theorem Corless.CM_apply (m : ℕ) (u : ℕ → ℂ) (i j : Fin m) :
    CM m u i j = if i = j then X else if (j : ℕ) = i + 1 then -C (u i)
      else if (i : ℕ) = j + 1 then C (u j) else 0 := by sorry
