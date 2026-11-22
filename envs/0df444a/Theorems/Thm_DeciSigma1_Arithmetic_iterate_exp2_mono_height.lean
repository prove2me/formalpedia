-- Prove2me | Theorems.Thm_DeciSigma1_Arithmetic_iterate_exp2_mono_height
-- name    : DeciSigma1.Arithmetic.iterate_exp2_mono_height
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:11:31.507351+00:00
-- url     : https://prove2.me/theorems/b9ffc4f6-63dd-4b16-9568-2463ef19b8e4
-- title:
--   Arithmetic: iterate exp2 mono height
-- statement:
--   Increasing the height increases an iterated exponential.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Arithmetic/ElementaryBounds.lean#L63-L64
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Arithmetic/ElementaryBounds.lean#L63-L64

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

theorem DeciSigma1.Arithmetic.iterate_exp2_mono_height (x : ℕ) : Monotone (fun h => exp2^[h] x) := by sorry
