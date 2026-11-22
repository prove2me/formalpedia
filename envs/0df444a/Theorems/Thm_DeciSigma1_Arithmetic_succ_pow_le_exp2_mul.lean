-- Prove2me | Theorems.Thm_DeciSigma1_Arithmetic_succ_pow_le_exp2_mul
-- name    : DeciSigma1.Arithmetic.succ_pow_le_exp2_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:11:34.691327+00:00
-- url     : https://prove2.me/theorems/5cac69dd-7042-4990-89e7-b1cc6923e8a2
-- title:
--   Arithmetic: succ pow le exp2 mul
-- statement:
--   A polynomial in `x + 1` is bounded by a single exponential.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Arithmetic/ElementaryBounds.lean#L81-L84
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Arithmetic/ElementaryBounds.lean#L81-L84

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

theorem DeciSigma1.Arithmetic.succ_pow_le_exp2_mul (x d : ℕ) : (x + 1) ^ d ≤ exp2 (d * x) := by sorry
