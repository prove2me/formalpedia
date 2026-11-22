-- Prove2me | Theorems.Thm_CircuitComplexity_or_size_complexity_le
-- name    : CircuitComplexity.or_size_complexity_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:15:15.349809+00:00
-- url     : https://prove2.me/theorems/1ce20502-9ec0-41c8-8bd7-10fd7b7fd88b
-- title:
--   Circuit Complexity: or size complexity le
-- statement:
--   The OR of two Boolean functions has circuit complexity bounded by the
--       sum of their individual complexities plus one (for the OR output gate).
--
--       Uses `ShannonUpper.binopCircuit` to compose two circuits side-by-side.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Nondeterminism.lean#L97-L114
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Nondeterminism.lean#L97-L114

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

theorem CircuitComplexity.or_size_complexity_le [CompleteBasis Basis.andOr2] [NeZero N]
    (g₁ g₂ : BitString N → Bool) :
    Circuit.sizeComplexity Basis.andOr2 (fun x => g₁ x || g₂ x) ≤
      Circuit.sizeComplexity Basis.andOr2 g₁ +
      Circuit.sizeComplexity Basis.andOr2 g₂ + 1 := by sorry
