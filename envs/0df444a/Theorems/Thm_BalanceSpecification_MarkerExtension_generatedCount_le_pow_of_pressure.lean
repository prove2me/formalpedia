-- Prove2me | Theorems.Thm_BalanceSpecification_MarkerExtension_generatedCount_le_pow_of_pressure
-- name    : BalanceSpecification.MarkerExtension.generatedCount_le_pow_of_pressure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:04:17.808612+00:00
-- url     : https://prove2.me/theorems/218630c9-b90d-4482-951b-a8dd447f8f54
-- title:
--   Marker Extension: generated Count le pow of pressure
-- statement:
--   A true weighted pressure bound for the actual code gives a pure
--   exponential bound on its actual finite-concatenation counts.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkedRenewal.lean#L90-L97
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkedRenewal.lean#L90-L97

module
public import Definitions.Def_BalanceSpecificaton_MarkerExtension
public import Definitions.Def_BalanceSpecificaton_RenewalBounds
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_MarkedRenewal
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.MarkerExtension
variable {A : Type*} [Fintype A]

theorem BalanceSpecification.MarkerExtension.generatedCount_le_pow_of_pressure (P : Set (Word A)) {ρ : ℝ} (hρ : 0 < ρ)
    (hpressure : ∀ n : ℕ,
      (∑ l ∈ Finset.range (n + 1), (generatorCount P (l + 1) : ℝ) / ρ ^ (l + 1)) ≤ 1)
    (n : ℕ) : (generatedCount P n : ℝ) ≤ ρ ^ n := by sorry
