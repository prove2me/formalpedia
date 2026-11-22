-- Prove2me | Theorems.Thm_CircuitComplexity_DNF_xorBool_complexity_lb
-- name    : CircuitComplexity.DNF.xorBool_complexity_lb
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:12:05.888854+00:00
-- url     : https://prove2.me/theorems/73508742-5aa3-4ba9-94f9-df1e8457703a
-- title:
--   DNF: xor Bool complexity lb
-- statement:
--   Any DNF computing N-variable XOR requires at least `2^{N-1}` terms.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/NF.lean#L42-L46
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/NF.lean#L42-L46

module
public import Definitions.Def_LeanPool_CircuitComplexity_NF_Defs
public import Definitions.Def_LeanPool_CircuitComplexity_XOR
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_NF
public import Definitions.Def_LeanPool_CircuitComplexity_NF
set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity

theorem CircuitComplexity.DNF.xorBool_complexity_lb (φ : DNF N) (hN : 1 ≤ N)
    (hcomp : ∀ x, φ.eval x = Schnorr.xorBool N x) :
    2 ^ (N - 1) ≤ φ.complexity := by sorry
