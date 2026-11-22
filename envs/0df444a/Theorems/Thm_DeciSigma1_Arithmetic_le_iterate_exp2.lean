-- Prove2me | Theorems.Thm_DeciSigma1_Arithmetic_le_iterate_exp2
-- name    : DeciSigma1.Arithmetic.le_iterate_exp2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:41:02.700943+00:00
-- url     : https://prove2.me/theorems/e1f11b4f-6039-49b0-affe-0e1f665e275d
-- title:
--   Arithmetic: le iterate exp2
-- statement:
--   Iterating the base-two exponential increases the argument.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Arithmetic/ElementaryBounds.lean#L55-L60
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Arithmetic/ElementaryBounds.lean#L55-L60

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

theorem DeciSigma1.Arithmetic.le_iterate_exp2 (h x : ℕ) : x ≤ exp2^[h] x := by sorry
