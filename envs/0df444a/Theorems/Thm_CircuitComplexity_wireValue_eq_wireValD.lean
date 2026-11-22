-- Prove2me | Theorems.Thm_CircuitComplexity_wireValue_eq_wireValD
-- name    : CircuitComplexity.wireValue_eq_wireValD
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:11:31.926799+00:00
-- url     : https://prove2.me/theorems/77bfb8d3-132e-400c-8c2c-09a12ba63a51
-- title:
--   Circuit Complexity: wire Value eq wire Val D
-- statement:
--   Wire values agree between `Circuit.wireValue` and `wireValD` for wires
--       in the range `0..N+G-1`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/Bridge.lean#L74-L125
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/Bridge.lean#L74-L125

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

theorem CircuitComplexity.wireValue_eq_wireValD {N G : Nat} [NeZero N]
    (c : Circuit Basis.andOr2 N 1 G)
    (input : BitString N) (w : Fin (N + G)) :
    c.wireValue input w =
      wireValD (circuitToDesc c) input ⟨w.val, by omega⟩ := by sorry
