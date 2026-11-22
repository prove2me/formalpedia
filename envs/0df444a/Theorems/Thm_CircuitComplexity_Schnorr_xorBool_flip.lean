-- Prove2me | Theorems.Thm_CircuitComplexity_Schnorr_xorBool_flip
-- name    : CircuitComplexity.Schnorr.xorBool_flip
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:09:09.822546+00:00
-- url     : https://prove2.me/theorems/840d9947-adc8-44a6-899b-79c02c739faf
-- title:
--   Schnorr: xor Bool flip
-- statement:
--   Flipping any input bit flips the XOR output.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/XOR.lean#L41-L63
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/XOR.lean#L41-L63

module
public import Definitions.Def_LeanPool_CircuitComplexity_Basic
public import Definitions.Def_LeanPool_CircuitComplexity_XOR
set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity
open CircuitComplexity.Schnorr

theorem CircuitComplexity.Schnorr.xorBool_flip (N : Nat) (x : BitString N) (a : Fin N) :
    xorBool N (Function.update x a (!x a)) = !xorBool N x := by sorry
