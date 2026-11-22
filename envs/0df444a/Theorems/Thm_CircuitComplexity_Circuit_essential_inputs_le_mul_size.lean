-- Prove2me | Theorems.Thm_CircuitComplexity_Circuit_essential_inputs_le_mul_size
-- name    : CircuitComplexity.Circuit.essential_inputs_le_mul_size
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:09:36.671257+00:00
-- url     : https://prove2.me/theorems/ceeac698-b00b-48c3-a336-73c46d290484
-- title:
--   Circuit: essential inputs le mul size
-- statement:
--   **Counting bound**: for bounded fan-in k, the number of essential
--       variables is at most k times the circuit size.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/LowerBound.lean#L146-L163
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/LowerBound.lean#L146-L163

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

theorem CircuitComplexity.Circuit.essential_inputs_le_mul_size {k : Nat}
    (c : Circuit (Basis.boundedAON k) N M G)
    (f : BitString N → BitString M)
    (hf : c.eval = f) :
    (EssentialInputs f).card ≤ k * c.size := by sorry
