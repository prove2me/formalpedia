-- Prove2me | Theorems.Thm_DeciSigma1_Arithmetic_iterate_exp2_add_le
-- name    : DeciSigma1.Arithmetic.iterate_exp2_add_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:38:49.697293+00:00
-- url     : https://prove2.me/theorems/019a6ce1-bb5d-4619-abdc-b45ca5943d6e
-- title:
--   Arithmetic: iterate exp2 add le
-- statement:
--   Sums at a fixed positive height are absorbed by summing the arguments.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Arithmetic/ElementaryBounds.lean#L104-L111
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Arithmetic/ElementaryBounds.lean#L104-L111

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

theorem DeciSigma1.Arithmetic.iterate_exp2_add_le (h a b : ℕ) (hh : 1 ≤ h) :
    exp2^[h] a + exp2^[h] b ≤ exp2^[h] (a + b + 1) := by sorry
