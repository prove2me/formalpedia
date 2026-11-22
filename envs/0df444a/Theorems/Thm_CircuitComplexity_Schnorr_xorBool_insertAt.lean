-- Prove2me | Theorems.Thm_CircuitComplexity_Schnorr_xorBool_insertAt
-- name    : CircuitComplexity.Schnorr.xorBool_insertAt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:11:11.105228+00:00
-- url     : https://prove2.me/theorems/4808adb0-aa59-4758-960f-ebdb781d1ebc
-- title:
--   Schnorr: xor Bool insert At
-- statement:
--   XOR with an inserted bit equals the inserted bit XORed with XOR of the rest.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/Schnorr.lean#L37-L61
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/Schnorr.lean#L37-L61

module
public import Definitions.Def_LeanPool_CircuitComplexity_XOR
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_CircDesc
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_Schnorr
set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity
open CircuitComplexity.Schnorr

theorem CircuitComplexity.Schnorr.xorBool_insertAt {N : Nat} (x : BitString N) (a : Fin (N + 1)) (b : Bool) :
    xorBool (N + 1) (insertAt x a b) = b.xor (xorBool N x) := by sorry
