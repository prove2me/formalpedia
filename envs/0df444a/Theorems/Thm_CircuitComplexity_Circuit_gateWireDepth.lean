-- Prove2me | Theorems.Thm_CircuitComplexity_Circuit_gateWireDepth
-- name    : CircuitComplexity.Circuit.gateWireDepth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:09:08.989085+00:00
-- url     : https://prove2.me/theorems/058ea6f0-4979-4e4a-9bae-6171b954b532
-- title:
--   Circuit: gate Wire Depth
-- statement:
--   Internal gate wires (index ≥ N) have depth 1 + max over their input wires.
--   Unfolds one step of `wireDepth` for the gate case.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Basic.lean#L170-L176
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Basic.lean#L170-L176

module
public import Mathlib.Order.Lattice.Nat
public import Definitions.Def_LeanPool_CircuitComplexity_Basic
set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity
open CircuitComplexity.Circuit
variable {B : Basis} {N M G : Nat} [NeZero N] [NeZero M]

theorem CircuitComplexity.Circuit.gateWireDepth (c : Circuit B N M G)
    (w : Fin (N + G)) (h : ¬ (w.val < N)) :
    c.wireDepth w =
      1 + Fin.foldl (c.gates ⟨w.val - N, by omega⟩).fanIn
        (fun acc k => max acc (c.wireDepth ((c.gates ⟨w.val - N, by omega⟩).inputs k))) 0 := by sorry
