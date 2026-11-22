-- Prove2me | Theorems.Thm_CircuitComplexity_Circuit_gate_elimination_lower_bound
-- name    : CircuitComplexity.Circuit.gate_elimination_lower_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:13:00.0709+00:00
-- url     : https://prove2.me/theorems/fa28c64c-238f-4872-864d-b3623f553f6f
-- title:
--   Circuit: gate elimination lower bound
-- statement:
--   **Gate elimination lower bound**: for fan-in k, circuit size is at
--       least ⌈n'/k⌉ where n' is the number of essential variables.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/LowerBound.lean#L167-L172
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/LowerBound.lean#L167-L172

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

theorem CircuitComplexity.Circuit.gate_elimination_lower_bound {k : Nat}
    (c : Circuit (Basis.boundedAON k) N M G)
    (f : BitString N → BitString M)
    (hf : c.eval = f) :
    (EssentialInputs f).card ≤ k * c.size := by sorry
