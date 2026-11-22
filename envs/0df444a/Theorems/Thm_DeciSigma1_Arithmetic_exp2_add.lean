-- Prove2me | Theorems.Thm_DeciSigma1_Arithmetic_exp2_add
-- name    : DeciSigma1.Arithmetic.exp2_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:34:24.405683+00:00
-- url     : https://prove2.me/theorems/dcf45b33-3f2e-434d-b3d5-c1639928594b
-- title:
--   Arithmetic: exp2 add
-- statement:
--   Multiplication of powers of two adds their exponents.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Arithmetic/ElementaryBounds.lean#L67-L67
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Arithmetic/ElementaryBounds.lean#L67-L67

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

theorem DeciSigma1.Arithmetic.exp2_add (a b : ℕ) : exp2 (a + b) = exp2 a * exp2 b := by sorry
