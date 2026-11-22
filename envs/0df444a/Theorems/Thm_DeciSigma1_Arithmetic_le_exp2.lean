-- Prove2me | Theorems.Thm_DeciSigma1_Arithmetic_le_exp2
-- name    : DeciSigma1.Arithmetic.le_exp2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:34:38.000313+00:00
-- url     : https://prove2.me/theorems/ce035af6-d712-4a4b-a051-69ed54597d09
-- title:
--   Arithmetic: le exp2
-- statement:
--   Every natural number is bounded by its base-two exponential.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Arithmetic/ElementaryBounds.lean#L49-L49
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Arithmetic/ElementaryBounds.lean#L49-L49

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

theorem DeciSigma1.Arithmetic.le_exp2 (x : ℕ) : x ≤ exp2 x := by sorry
