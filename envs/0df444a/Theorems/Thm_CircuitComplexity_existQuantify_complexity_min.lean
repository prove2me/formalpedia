-- Prove2me | Theorems.Thm_CircuitComplexity_existQuantify_complexity_min
-- name    : CircuitComplexity.existQuantify_complexity_min
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:15:13.862807+00:00
-- url     : https://prove2.me/theorems/8d24df1e-185c-4721-9769-da5e23a50708
-- title:
--   Circuit Complexity: exist Quantify complexity min
-- statement:
--   **Combined upper bound**: the minimum of the naive and Shannon bounds.
--
--       When `sizeComplexity(f) ≈ 2^(k+m)/2`, the Shannon bound
--       `18 · 2^m / m` is exponentially better than the naive
--       `2^k · (s + 1)`, especially for large `k`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Nondeterminism.lean#L224-L228
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Nondeterminism.lean#L224-L228

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

theorem CircuitComplexity.existQuantify_complexity_min [CompleteBasis Basis.andOr2]
    (f : BitString (k + m) → Bool) [NeZero m] (hm : 16 ≤ m) :
    Circuit.sizeComplexity Basis.andOr2 (existQuantify f) ≤
      min (2 ^ k * (Circuit.sizeComplexity Basis.andOr2 f + 1)) (18 * 2 ^ m / m) := by sorry
