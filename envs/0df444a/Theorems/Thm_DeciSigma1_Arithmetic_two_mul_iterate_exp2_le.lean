-- Prove2me | Theorems.Thm_DeciSigma1_Arithmetic_two_mul_iterate_exp2_le
-- name    : DeciSigma1.Arithmetic.two_mul_iterate_exp2_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:41:13.591928+00:00
-- url     : https://prove2.me/theorems/358e4367-ef92-4ded-98fa-6cc6039672bd
-- title:
--   Arithmetic: two mul iterate exp2 le
-- statement:
--   Increasing the argument by one at least doubles a positive-height iterate.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Arithmetic/ElementaryBounds.lean#L93-L101
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Arithmetic/ElementaryBounds.lean#L93-L101

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

theorem DeciSigma1.Arithmetic.two_mul_iterate_exp2_le (h x : ℕ) (hh : 1 ≤ h) :
    2 * exp2^[h] x ≤ exp2^[h] (x + 1) := by sorry
