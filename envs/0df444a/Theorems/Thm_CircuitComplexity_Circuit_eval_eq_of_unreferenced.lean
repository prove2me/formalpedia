-- Prove2me | Theorems.Thm_CircuitComplexity_Circuit_eval_eq_of_unreferenced
-- name    : CircuitComplexity.Circuit.eval_eq_of_unreferenced
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:10:24.480122+00:00
-- url     : https://prove2.me/theorems/ff1ec976-b6e5-46be-b394-ce4d44252972
-- title:
--   Circuit: eval eq of unreferenced
-- statement:
--   If no gate (internal or output) reads primary input `i`, the circuit
--       output is unchanged when input `i` is modified.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/LowerBound.lean#L59-L69
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/LowerBound.lean#L59-L69

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

theorem CircuitComplexity.Circuit.eval_eq_of_unreferenced
    (c : Circuit B N M G) (i : Fin N) (b : Bool)
    (hno_gates : ∀ g : Fin G, ∀ k : Fin (c.gates g).fanIn,
      ((c.gates g).inputs k).val ≠ i.val)
    (hno_outputs : ∀ j : Fin M, ∀ k : Fin (c.outputs j).fanIn,
      ((c.outputs j).inputs k).val ≠ i.val)
    (x : BitString N) :
    c.eval x = c.eval (Function.update x i b) := by sorry
