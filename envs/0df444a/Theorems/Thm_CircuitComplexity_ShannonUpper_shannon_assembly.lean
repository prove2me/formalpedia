-- Prove2me | Theorems.Thm_CircuitComplexity_ShannonUpper_shannon_assembly
-- name    : CircuitComplexity.ShannonUpper.shannon_assembly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:11:47.350881+00:00
-- url     : https://prove2.me/theorems/e219d54c-4609-4e71-844d-c92466ad4207
-- title:
--   Shannon Upper: shannon assembly
-- statement:
--   The Shannon Upper construction uses the shannon assembly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/ShannonUpper.lean#L1772-L1781
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/ShannonUpper.lean#L1772-L1781

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

theorem CircuitComplexity.ShannonUpper.shannon_assembly (N : Nat) [NeZero N] (hN : 16 ≤ N)
    (f : BitString N → Bool) :
    ∃ G, ∃ c : Circuit Basis.andOr2 N 1 G,
      (fun x => (c.eval x) 0) = f ∧
      G + 1 ≤ 4 * 2 ^ dataBits N + 2 * 2 ^ addrBits N +
          2 ^ (2 ^ addrBits N + addrBits N) := by sorry
