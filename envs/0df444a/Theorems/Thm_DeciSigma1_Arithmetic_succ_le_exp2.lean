-- Prove2me | Theorems.Thm_DeciSigma1_Arithmetic_succ_le_exp2
-- name    : DeciSigma1.Arithmetic.succ_le_exp2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:34:45.525799+00:00
-- url     : https://prove2.me/theorems/6747f95c-a143-4249-ba37-63c8aa5e9ab9
-- title:
--   Arithmetic: succ le exp2
-- statement:
--   Every natural number is smaller than its base-two exponential.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Arithmetic/ElementaryBounds.lean#L46-L46
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Arithmetic/ElementaryBounds.lean#L46-L46

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

theorem DeciSigma1.Arithmetic.succ_le_exp2 (x : ℕ) : x + 1 ≤ exp2 x := by sorry
