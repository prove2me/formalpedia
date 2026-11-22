-- Prove2me | Theorems.Thm_CircuitComplexity_existQuantify_complexity_shannon
-- name    : CircuitComplexity.existQuantify_complexity_shannon
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:15:05.777811+00:00
-- url     : https://prove2.me/theorems/752fa2f3-4c35-42ad-87bb-ec530c599213
-- title:
--   Circuit Complexity: exist Quantify complexity shannon
-- statement:
--   **Shannon upper bound for existential quantification.**
--
--       The quantified function `existQuantify f : BitString m → Bool` is just
--       an `m`-input Boolean function, so the Shannon upper bound applies
--       unconditionally.  Even if `f` has exponential circuit complexity,
--       `existQuantify f` has complexity at most `O(2^m / m)`, which decreases
--       exponentially as more variables are quantified away.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Nondeterminism.lean#L214-L217
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Nondeterminism.lean#L214-L217

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

theorem CircuitComplexity.existQuantify_complexity_shannon
    (f : BitString (k + m) → Bool) [NeZero m] (hm : 16 ≤ m) :
    Circuit.sizeComplexity Basis.andOr2 (existQuantify f) ≤ 18 * 2 ^ m / m := by sorry
