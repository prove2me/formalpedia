-- Prove2me | Theorems.Thm_DeciSigma1_Arithmetic_exp2_mono
-- name    : DeciSigma1.Arithmetic.exp2_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:34:23.824575+00:00
-- url     : https://prove2.me/theorems/d573a5da-4867-4c9b-8f2b-9aebbd40ea9c
-- title:
--   Arithmetic: exp2 mono
-- statement:
--   The base-two exponential is increasing.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Arithmetic/ElementaryBounds.lean#L43-L43
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Arithmetic/ElementaryBounds.lean#L43-L43

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

theorem DeciSigma1.Arithmetic.exp2_mono : Monotone exp2 := by sorry
