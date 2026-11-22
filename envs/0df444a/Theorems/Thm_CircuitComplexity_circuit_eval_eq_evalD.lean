-- Prove2me | Theorems.Thm_CircuitComplexity_circuit_eval_eq_evalD
-- name    : CircuitComplexity.circuit_eval_eq_evalD
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:11:39.278353+00:00
-- url     : https://prove2.me/theorems/d2057c44-c07b-4df7-aaf8-84558b1b5f89
-- title:
--   Circuit Complexity: circuit eval eq eval D
-- statement:
--   Circuit evaluation agrees with descriptor evaluation.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/Bridge.lean#L128-L146
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/Bridge.lean#L128-L146

module
public import Definitions.Def_LeanPool_CircuitComplexity_AON_Defs
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_CircDesc
public import Definitions.Def_LeanPool_CircuitComplexity_XOR
public import Mathlib.Algebra.GroupWithZero.Nat
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_Schnorr
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_Bridge
set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity

theorem CircuitComplexity.circuit_eval_eq_evalD {N G : Nat} [NeZero N]
    (c : Circuit Basis.andOr2 N 1 G) :
    (fun x => (c.eval x) 0) = evalD (Nat.succ_pos G) (circuitToDesc c) := by sorry
