-- Prove2me | Theorems.Thm_CircuitComplexity_ShannonUpper_shannon_arithmetic
-- name    : CircuitComplexity.ShannonUpper.shannon_arithmetic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:11:47.320797+00:00
-- url     : https://prove2.me/theorems/7371424d-3d74-4114-94f9-a9c5089080a5
-- title:
--   Shannon Upper: shannon arithmetic
-- statement:
--   The Shannon Upper construction uses the shannon arithmetic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/ShannonUpper.lean#L443-L449
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/ShannonUpper.lean#L443-L449

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

theorem CircuitComplexity.ShannonUpper.shannon_arithmetic (N : Nat) (hN : 16 ≤ N) :
    (4 * 2 ^ dataBits N + 2 * 2 ^ addrBits N +
      2 ^ (2 ^ addrBits N + addrBits N)) * N ≤ 18 * 2 ^ N := by sorry
