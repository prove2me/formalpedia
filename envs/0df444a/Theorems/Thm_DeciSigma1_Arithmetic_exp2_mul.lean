-- Prove2me | Theorems.Thm_DeciSigma1_Arithmetic_exp2_mul
-- name    : DeciSigma1.Arithmetic.exp2_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:34:38.980927+00:00
-- url     : https://prove2.me/theorems/eb0bea3b-9a83-4a66-9b30-25affe0e1241
-- title:
--   Arithmetic: exp2 mul
-- statement:
--   A power of a power of two multiplies the exponent.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Arithmetic/ElementaryBounds.lean#L70-L70
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Arithmetic/ElementaryBounds.lean#L70-L70

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

theorem DeciSigma1.Arithmetic.exp2_mul (a b : ℕ) : exp2 (a * b) = exp2 a ^ b := by sorry
