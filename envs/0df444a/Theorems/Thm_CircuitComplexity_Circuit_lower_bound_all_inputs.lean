-- Prove2me | Theorems.Thm_CircuitComplexity_Circuit_lower_bound_all_inputs
-- name    : CircuitComplexity.Circuit.lower_bound_all_inputs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:13:06.217285+00:00
-- url     : https://prove2.me/theorems/5b3f90e3-908e-41af-92d2-e341ba9f97d4
-- title:
--   Circuit: lower bound all inputs
-- statement:
--   Corollary: if `f` depends on all N inputs, then N ≤ k · size.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/LowerBound.lean#L175-L184
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/LowerBound.lean#L175-L184

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

theorem CircuitComplexity.Circuit.lower_bound_all_inputs {k : Nat}
    (c : Circuit (Basis.boundedAON k) N M G)
    (f : BitString N → BitString M)
    (hf : c.eval = f)
    (hall : ∀ i : Fin N, IsEssentialInput f i) :
    N ≤ k * c.size := by sorry
