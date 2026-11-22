-- Prove2me | Theorems.Thm_CircuitComplexity_ShannonUpper_binopCircuit_or_correct
-- name    : CircuitComplexity.ShannonUpper.binopCircuit_or_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:11:43.969881+00:00
-- url     : https://prove2.me/theorems/babee405-8053-4d5d-8d13-dc97b98653af
-- title:
--   Shannon Upper: binop Circuit or correct
-- statement:
--   `binopCircuit` correctly computes the OR of two circuits' outputs.
--
--       The output gate of `binopCircuit` applies OR to wires `N + G₁` and
--       `N + G₁ + G₂ + 1`, which replicate the output gates of c₁ and c₂.
--       The proof shows that wire values in the combined circuit agree with
--       wire values in the original circuits (via `binop_wireValue_c₁` and
--       `binop_wireValue_c₂`), then combines.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/ShannonUpper.lean#L248-L298
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/ShannonUpper.lean#L248-L298

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

theorem CircuitComplexity.ShannonUpper.binopCircuit_or_correct {N G₁ G₂ : Nat} [NeZero N]
    (c₁ : Circuit Basis.andOr2 N 1 G₁) (c₂ : Circuit Basis.andOr2 N 1 G₂)
    (f₁ f₂ : BitString N → Bool)
    (hf₁ : (fun x => (c₁.eval x) 0) = f₁)
    (hf₂ : (fun x => (c₂.eval x) 0) = f₂) :
    (fun x => ((binopCircuit AONOp.or c₁ c₂).eval x) 0) =
    fun x => f₁ x || f₂ x := by sorry
