-- Prove2me | Theorems.Thm_CircuitComplexity_existQuantify_complexity_le
-- name    : CircuitComplexity.existQuantify_complexity_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:15:01.885801+00:00
-- url     : https://prove2.me/theorems/e55e335d-54d7-4b23-912d-38c16c76ce33
-- title:
--   Circuit Complexity: exist Quantify complexity le
-- statement:
--   **Naive upper bound for existential quantification.**
--
--       If `f : BitString (k + m) → Bool` has fan-in-2 AND/OR circuit complexity
--       `s`, then `existQuantify f : BitString m → Bool` has circuit complexity
--       at most `2^k · (s + 1)`.
--
--       **Proof.**  By induction on `k`.  We prove the tighter statement
--       `sizeComplexity + 1 ≤ 2^k · (s + 1)`, which absorbs the OR-gate
--       overhead at each step.
--
--       * **Base case** (`k = 0`):  `existQuantify` is the identity (up to a
--         transport along `0 + m = m`), so complexity is preserved.
--
--       * **Inductive step** (`k → k + 1`):  `existQuantify (k+1) f` factors
--         as `(existQuantify k (f|₀)) OR (existQuantify k (f|₁))` via
--         `existQuantify_succ`.  Restriction preserves complexity; the OR adds
--         one gate; and the inductive hypothesis bounds each branch by
--         `2^k · (s + 1) − 1`.  After the "+1 trick":
--         `(size₁ + size₂ + 1) + 1 = (size₁ + 1) + (size₂ + 1) ≤ 2^(k+1) · (s + 1)`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Nondeterminism.lean#L160-L205
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Nondeterminism.lean#L160-L205

module
public import Definitions.Def_LeanPool_CircuitComplexity_Nondeterminism_Defs
public import Definitions.Def_LeanPool_CircuitComplexity_AON_Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_Nondeterminism
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_ShannonUpper
public import Definitions.Def_LeanPool_CircuitComplexity_Shannon
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_CircuitComplexity_Nondeterminism
set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity
variable {k m : Nat}

theorem CircuitComplexity.existQuantify_complexity_le [CompleteBasis Basis.andOr2]
    (f : BitString (k + m) → Bool) [NeZero m] :
    Circuit.sizeComplexity Basis.andOr2 (existQuantify f) ≤
      2 ^ k * (Circuit.sizeComplexity Basis.andOr2 f + 1) := by sorry
