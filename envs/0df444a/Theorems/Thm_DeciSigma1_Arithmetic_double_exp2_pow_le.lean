-- Prove2me | Theorems.Thm_DeciSigma1_Arithmetic_double_exp2_pow_le
-- name    : DeciSigma1.Arithmetic.double_exp2_pow_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:41:12.224437+00:00
-- url     : https://prove2.me/theorems/22cbd57c-6b7f-4d87-98b8-93685202357a
-- title:
--   Arithmetic: double exp2 pow le
-- statement:
--   A power of a double exponential is absorbed in its inner argument.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Arithmetic/ElementaryBounds.lean#L87-L90
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Arithmetic/ElementaryBounds.lean#L87-L90

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

theorem DeciSigma1.Arithmetic.double_exp2_pow_le (a c : ℕ) : (exp2 (exp2 a)) ^ c ≤
    exp2 (exp2 (a + c)) := by sorry
