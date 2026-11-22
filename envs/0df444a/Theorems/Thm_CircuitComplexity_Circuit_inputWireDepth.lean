-- Prove2me | Theorems.Thm_CircuitComplexity_Circuit_inputWireDepth
-- name    : CircuitComplexity.Circuit.inputWireDepth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:08:53.858583+00:00
-- url     : https://prove2.me/theorems/8136f601-af53-4a23-a1bb-57521e0485cf
-- title:
--   Circuit: input Wire Depth
-- statement:
--   Primary input wires (index < N) have depth 0.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Basic.lean#L163-L166
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Basic.lean#L163-L166

module
public import Mathlib.Order.Lattice.Nat
public import Definitions.Def_LeanPool_CircuitComplexity_Basic
set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity
open CircuitComplexity.Circuit
variable {B : Basis} {N M G : Nat} [NeZero N] [NeZero M]

theorem CircuitComplexity.Circuit.inputWireDepth (c : Circuit B N M G)
    (w : Fin (N + G)) (h : w.val < N) :
    c.wireDepth w = 0 := by sorry
