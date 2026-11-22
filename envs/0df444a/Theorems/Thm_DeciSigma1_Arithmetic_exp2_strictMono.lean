-- Prove2me | Theorems.Thm_DeciSigma1_Arithmetic_exp2_strictMono
-- name    : DeciSigma1.Arithmetic.exp2_strictMono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:38:43.19379+00:00
-- url     : https://prove2.me/theorems/7b8a71c0-c912-445b-8bdc-abb32c7f7934
-- title:
--   Arithmetic: exp2 strict Mono
-- statement:
--   The base-two exponential is strictly increasing.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Arithmetic/ElementaryBounds.lean#L38-L40
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Arithmetic/ElementaryBounds.lean#L38-L40

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

theorem DeciSigma1.Arithmetic.exp2_strictMono : StrictMono exp2 := by sorry
