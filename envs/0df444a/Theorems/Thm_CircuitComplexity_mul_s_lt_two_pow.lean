-- Prove2me | Theorems.Thm_CircuitComplexity_mul_s_lt_two_pow
-- name    : CircuitComplexity.mul_s_lt_two_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:10:43.716806+00:00
-- url     : https://prove2.me/theorems/4142defe-e0a9-410e-bdfe-8da3fb687b39
-- title:
--   Circuit Complexity: mul s lt two pow
-- statement:
--   The exponent `(2N+3) * s` is less than `2^N`, which ensures the
--       power-of-two bound in the main arithmetic inequality.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/CircDesc.lean#L112-L117
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/CircDesc.lean#L112-L117

module
public import Definitions.Def_LeanPool_CircuitComplexity_Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_CircDesc
set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity

theorem CircuitComplexity.mul_s_lt_two_pow (N : Nat) (hN : 6 ≤ N) :
    (2 * N + 3) * (2 ^ N / (5 * N)) < 2 ^ N := by sorry
