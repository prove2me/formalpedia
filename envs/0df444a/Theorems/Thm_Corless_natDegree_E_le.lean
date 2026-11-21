-- Prove2me | Theorems.Thm_Corless_natDegree_E_le
-- name    : Corless.natDegree_E_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:41:50.256406+00:00
-- url     : https://prove2.me/theorems/8eb70de7-36df-4a69-8952-948ec30c9ef9
-- title:
--   Corless: nat Degree E le
-- statement:
--   The Corless construction uses the nat Degree E le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CorlessNilpotent/Matrix.lean#L127-L134
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CorlessNilpotent/Matrix.lean#L127-L134

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

theorem Corless.natDegree_E_le (s : ℕ → ℤ) (j : ℕ) : (E s j).natDegree ≤ j := by sorry
