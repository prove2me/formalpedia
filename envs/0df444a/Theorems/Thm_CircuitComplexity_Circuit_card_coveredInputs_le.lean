-- Prove2me | Theorems.Thm_CircuitComplexity_Circuit_card_coveredInputs_le
-- name    : CircuitComplexity.Circuit.card_coveredInputs_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:10:31.872017+00:00
-- url     : https://prove2.me/theorems/8d674673-0db9-4e60-975c-2b2d6a7a0b17
-- title:
--   Circuit: card covered Inputs le
-- statement:
--   The Circuit construction uses the card covered Inputs le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/LowerBound.lean#L100-L115
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/LowerBound.lean#L100-L115

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

theorem CircuitComplexity.Circuit.card_coveredInputs_le (g : Gate B (N + G)) :
    (coveredInputs g : Finset (Fin N)).card ≤ g.fanIn := by sorry
