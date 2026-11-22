-- Prove2me | Theorems.Thm_CircuitComplexity_ShannonUpper_shannon_construction
-- name    : CircuitComplexity.ShannonUpper.shannon_construction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:11:46.858934+00:00
-- url     : https://prove2.me/theorems/0bb40d39-e49c-40c9-b496-eb81a31f7e87
-- title:
--   Shannon Upper: shannon construction
-- statement:
--   **Shannon circuit construction**: For `N ≥ 16`, every Boolean function
--       has a fan-in-2 AND/OR circuit of size `≤ 18 · 2^N / N`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/ShannonUpper.lean#L1787-L1792
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/ShannonUpper.lean#L1787-L1792

module
public import Definitions.Def_LeanPool_CircuitComplexity_AON_Defs
public import Mathlib.Data.Nat.Log
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_ShannonUpper
set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity
open CircuitComplexity.ShannonUpper

theorem CircuitComplexity.ShannonUpper.shannon_construction (N : Nat) [NeZero N] (hN : 16 ≤ N)
    (f : BitString N → Bool) :
    ∃ G, ∃ c : Circuit Basis.andOr2 N 1 G,
      (fun x => (c.eval x) 0) = f ∧ c.size ≤ 18 * 2 ^ N / N := by sorry
