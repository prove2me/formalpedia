-- Prove2me | Theorems.Thm_CircuitComplexity_Schnorr_xor_lower_bound_2
-- name    : CircuitComplexity.Schnorr.xor_lower_bound_2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:11:19.168732+00:00
-- url     : https://prove2.me/theorems/8e94f5d8-6ea0-420f-92c0-2e350f6185fb
-- title:
--   Schnorr: xor lower bound 2
-- statement:
--   Any DeMorgan circuit computing XOR_N (or complement) has ≥ 2N - 1 gates.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/Schnorr.lean#L1415-L1430
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/Schnorr.lean#L1415-L1430

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

theorem CircuitComplexity.Schnorr.xor_lower_bound_2 (N s : Nat) (hs : 0 < s) (d : CircDesc N s) (comp : Bool)
    (heval : ∀ x, evalD hs d x = comp.xor (xorBool N x))
    (hN : 1 ≤ N) : s + 1 ≥ 2 * N := by sorry
