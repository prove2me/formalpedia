-- Prove2me | Theorems.Thm_CircuitComplexity_ShannonUpper_shannon_size_le
-- name    : CircuitComplexity.ShannonUpper.shannon_size_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:11:48.016612+00:00
-- url     : https://prove2.me/theorems/97cd5c08-66ae-4f71-8e61-fba4fa9407e1
-- title:
--   Shannon Upper: shannon size le
-- statement:
--   The Shannon Upper construction uses the shannon size le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/ShannonUpper.lean#L451-L461
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/ShannonUpper.lean#L451-L461

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

theorem CircuitComplexity.ShannonUpper.shannon_size_le (N : Nat) (hN : 16 ≤ N) (G : Nat)
    (hG : G + 1 ≤ 4 * 2 ^ dataBits N + 2 * 2 ^ addrBits N +
            2 ^ (2 ^ addrBits N + addrBits N)) :
    G + 1 ≤ 18 * 2 ^ N / N := by sorry
