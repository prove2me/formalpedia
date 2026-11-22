-- Prove2me | Theorems.Thm_CircuitComplexity_restrictCircuit_eval
-- name    : CircuitComplexity.restrictCircuit_eval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:14:29.153192+00:00
-- url     : https://prove2.me/theorems/8fcbbe91-820f-4b01-9fb9-a8a764f4e57d
-- title:
--   Circuit Complexity: restrict Circuit eval
-- statement:
--   The restricted circuit computes `restrictFirst f b`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/Nondeterminism.lean#L273-L288
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/Nondeterminism.lean#L273-L288

module
public import Definitions.Def_LeanPool_CircuitComplexity_Nondeterminism_Defs
public import Definitions.Def_LeanPool_CircuitComplexity_AON_Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_Nondeterminism
set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity
variable {k m : Nat}

theorem CircuitComplexity.restrictCircuit_eval {G : Nat} [NeZero m] (b : Bool)
    (c : Circuit Basis.andOr2 ((k + 1) + m) 1 G)
    (f : BitString ((k + 1) + m) → Bool)
    (heval : (fun x => (c.eval x) 0) = f) :
    (fun x => ((restrictCircuit (k := k) b c).eval x) 0) = restrictFirst f b := by sorry
