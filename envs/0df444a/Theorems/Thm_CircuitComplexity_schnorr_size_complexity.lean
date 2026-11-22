-- Prove2me | Theorems.Thm_CircuitComplexity_schnorr_size_complexity
-- name    : CircuitComplexity.schnorr_size_complexity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:13:10.008201+00:00
-- url     : https://prove2.me/theorems/4dea0103-6d04-4df3-ac8d-8f804191de6b
-- title:
--   Circuit Complexity: schnorr size complexity
-- statement:
--   **Schnorr lower bound in terms of `sizeComplexity`**: the fan-in-2
--       AND/OR circuit complexity of N-input XOR is at least `2N − 1`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Schnorr.lean#L58-L67
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Schnorr.lean#L58-L67

module
public import Definitions.Def_LeanPool_CircuitComplexity_XOR
public import Definitions.Def_LeanPool_CircuitComplexity_AON_Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_Bridge
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Definitions.Def_LeanPool_CircuitComplexity_Schnorr
set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity

theorem CircuitComplexity.schnorr_size_complexity (N : Nat) [NeZero N] (hN : 1 ≤ N)
    [CompleteBasis Basis.andOr2] :
    Circuit.sizeComplexity Basis.andOr2 (Schnorr.xorBool N) ≥ 2 * N - 1 := by sorry
