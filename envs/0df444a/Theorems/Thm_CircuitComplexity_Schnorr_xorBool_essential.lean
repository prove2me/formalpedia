-- Prove2me | Theorems.Thm_CircuitComplexity_Schnorr_xorBool_essential
-- name    : CircuitComplexity.Schnorr.xorBool_essential
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:11:17.106773+00:00
-- url     : https://prove2.me/theorems/5ac3f162-1244-49de-a916-3302d2854606
-- title:
--   Schnorr: xor Bool essential
-- statement:
--   XOR depends on all inputs.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/XOR.lean#L66-L68
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/XOR.lean#L66-L68

module
public import Definitions.Def_LeanPool_CircuitComplexity_Basic
public import Definitions.Def_LeanPool_CircuitComplexity_XOR
set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity
open CircuitComplexity.Schnorr

theorem CircuitComplexity.Schnorr.xorBool_essential (N : Nat) (a : Fin N) (x : BitString N) :
    xorBool N x ≠ xorBool N (Function.update x a (!x a)) := by sorry
