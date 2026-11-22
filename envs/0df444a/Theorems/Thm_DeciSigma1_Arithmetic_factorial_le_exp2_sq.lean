-- Prove2me | Theorems.Thm_DeciSigma1_Arithmetic_factorial_le_exp2_sq
-- name    : DeciSigma1.Arithmetic.factorial_le_exp2_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:38:08.868813+00:00
-- url     : https://prove2.me/theorems/8a4b0b0d-4d3a-433e-be10-528a013eb01f
-- title:
--   Arithmetic: factorial le exp2 sq
-- statement:
--   A factorial is bounded by a single exponential with quadratic exponent.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Arithmetic/ElementaryBounds.lean#L125-L129
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Arithmetic/ElementaryBounds.lean#L125-L129

module
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Order.Iterate
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Order.Monotone.Defs
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_ElementaryBounds
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Arithmetic

theorem DeciSigma1.Arithmetic.factorial_le_exp2_sq (n : ℕ) : n.factorial ≤ exp2 (n * n) := by sorry
