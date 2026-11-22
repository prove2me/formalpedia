-- Prove2me | Theorems.Thm_CircuitComplexity_Circuit_exists_gate_reads_input
-- name    : CircuitComplexity.Circuit.exists_gate_reads_input
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:10:28.725201+00:00
-- url     : https://prove2.me/theorems/d2d7b2ae-774b-4a21-9b75-b6989dccafdf
-- title:
--   Circuit: exists gate reads input
-- statement:
--   If `c` computes `f` and `f` depends on variable `i`, some gate
--       (internal or output) directly reads input wire `i`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/LowerBound.lean#L75-L86
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/LowerBound.lean#L75-L86

module
public import Definitions.Def_LeanPool_CircuitComplexity_EssentialInput
public import Definitions.Def_LeanPool_CircuitComplexity_AON_Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Sum
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_LowerBound
set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity
open CircuitComplexity.Circuit
variable {B : Basis} {N M G : Nat} [NeZero N] [NeZero M]

theorem CircuitComplexity.Circuit.exists_gate_reads_input
    (c : Circuit B N M G) (f : BitString N → BitString M)
    (hf : c.eval = f) (i : Fin N) (hdep : IsEssentialInput f i) :
    (∃ g : Fin G, ∃ k : Fin (c.gates g).fanIn,
      ((c.gates g).inputs k).val = i.val) ∨
    (∃ j : Fin M, ∃ k : Fin (c.outputs j).fanIn,
      ((c.outputs j).inputs k).val = i.val) := by sorry
