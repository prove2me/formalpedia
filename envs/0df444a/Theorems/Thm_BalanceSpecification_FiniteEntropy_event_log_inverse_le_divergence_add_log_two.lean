-- Prove2me | Theorems.Thm_BalanceSpecification_FiniteEntropy_event_log_inverse_le_divergence_add_log_two
-- name    : BalanceSpecification.FiniteEntropy.event_log_inverse_le_divergence_add_log_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:10:13.89239+00:00
-- url     : https://prove2.me/theorems/3eaa587b-e8ff-487f-81cf-f57e0ce4c018
-- title:
--   Finite Entropy: event log inverse le divergence add log two
-- statement:
--   A finite relative entropy bound controls the mass assigned to a rare event.
--   The proof uses a subprobability exponential tilt, including zero first weights.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/AbsoluteContinuity.lean#L22-L79
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/AbsoluteContinuity.lean#L22-L79

module
public import Definitions.Def_BalanceSpecificaton_EntropyAlgebra
public import Definitions.Def_BalanceSpecificaton_CylinderAlgebra
public import Definitions.Def_BalanceSpecificaton_BlockEntropy
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_AbsoluteContinuity
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.FiniteEntropy
variable {ι : Type*} [Fintype ι]

theorem BalanceSpecification.FiniteEntropy.event_log_inverse_le_divergence_add_log_two
    {p q : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 < q i)
    (hpsum : ∑ i, p i = 1) (hqsum : ∑ i, q i = 1)
    (S : Finset ι) (hQ : 0 < ∑ i ∈ S, q i) :
    (∑ i ∈ S, p i) * Real.log (1 / (∑ i ∈ S, q i)) ≤
      divergence p q + Real.log 2 := by sorry
