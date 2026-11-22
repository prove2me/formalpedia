-- Prove2me | Theorems.Thm_DeciSigma1_Arithmetic_exp2_add_le
-- name    : DeciSigma1.Arithmetic.exp2_add_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:38:08.334355+00:00
-- url     : https://prove2.me/theorems/f308ef1e-78ce-47a7-b4f6-d392e2588db1
-- title:
--   Arithmetic: exp2 add le
-- statement:
--   A sum of two powers of two is absorbed with one additional exponent unit.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Arithmetic/ElementaryBounds.lean#L73-L78
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Arithmetic/ElementaryBounds.lean#L73-L78

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

theorem DeciSigma1.Arithmetic.exp2_add_le (a b : ℕ) : exp2 a + exp2 b ≤ exp2 (a + b + 1) := by sorry
