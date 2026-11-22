-- Prove2me | Theorems.Thm_CircuitComplexity_Circuit_boundedAON_coveredInputs_card_le
-- name    : CircuitComplexity.Circuit.boundedAON_coveredInputs_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:10:29.894545+00:00
-- url     : https://prove2.me/theorems/e13f0cc6-5978-4823-a14c-9708f9017095
-- title:
--   Circuit: bounded AON covered Inputs card le
-- statement:
--   For a gate over bounded fan-in k AON basis, covered inputs has card ≤ k.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/LowerBound.lean#L118-L124
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/LowerBound.lean#L118-L124

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

theorem CircuitComplexity.Circuit.boundedAON_coveredInputs_card_le {k : Nat}
    (g : Gate (Basis.boundedAON k) (N + G)) :
    (coveredInputs g : Finset (Fin N)).card ≤ k := by sorry
