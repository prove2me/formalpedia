-- Prove2me | Theorems.Thm_DeciSigma1_Arithmetic_iterate_exp2_mul_le
-- name    : DeciSigma1.Arithmetic.iterate_exp2_mul_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:41:12.878947+00:00
-- url     : https://prove2.me/theorems/0ce4fdbe-db67-45e6-a513-3a81b263d0a6
-- title:
--   Arithmetic: iterate exp2 mul le
-- statement:
--   Products at a fixed positive height are absorbed by summing the arguments.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Arithmetic/ElementaryBounds.lean#L114-L122
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Arithmetic/ElementaryBounds.lean#L114-L122

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

theorem DeciSigma1.Arithmetic.iterate_exp2_mul_le (h a b : ℕ) (hh : 1 ≤ h) :
    exp2^[h] a * exp2^[h] b ≤ exp2^[h] (a + b + 1) := by sorry
