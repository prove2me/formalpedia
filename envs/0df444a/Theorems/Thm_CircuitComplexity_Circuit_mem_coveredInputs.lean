-- Prove2me | Theorems.Thm_CircuitComplexity_Circuit_mem_coveredInputs
-- name    : CircuitComplexity.Circuit.mem_coveredInputs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:09:35.618496+00:00
-- url     : https://prove2.me/theorems/413a1184-41ad-418d-99ab-05b283e1ed1a
-- title:
--   Circuit: mem covered Inputs
-- statement:
--   The Circuit construction uses the mem covered Inputs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/LowerBound.lean#L96-L98
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/LowerBound.lean#L96-L98

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
omit [NeZero N]

theorem CircuitComplexity.Circuit.mem_coveredInputs (g : Gate B (N + G)) (i : Fin N) :
    i ∈ coveredInputs g ↔ ∃ k : Fin g.fanIn, (g.inputs k).val = i.val := by sorry
