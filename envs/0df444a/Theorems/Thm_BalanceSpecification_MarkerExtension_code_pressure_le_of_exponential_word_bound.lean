-- Prove2me | Theorems.Thm_BalanceSpecification_MarkerExtension_code_pressure_le_of_exponential_word_bound
-- name    : BalanceSpecification.MarkerExtension.code_pressure_le_of_exponential_word_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:03:45.712098+00:00
-- url     : https://prove2.me/theorems/2e791088-c3c9-4376-8d2e-a7f13ce80021
-- title:
--   Marker Extension: code pressure le of exponential word bound
-- statement:
--   The proved source word-growth envelope and the chosen sparse numerical
--   budget give the corresponding bound on the actual code's pressure.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerCodeCounts.lean#L179-L198
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerCodeCounts.lean#L179-L198

module
public import Definitions.Def_BalanceSpecificaton_MarkerExtension
public import Definitions.Def_BalanceSpecificaton_MarkerEstimates
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_MarkerCodeCounts
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.MarkerExtension
open scoped Classical
variable {A : Type*} [TopologicalSpace A] [Fintype A] {Y : ShiftSpace A}
variable (M : ℕ)
  (hM : ∀ u ∈ language Y, ∀ v ∈ language Y,
    ∃ b ∈ language Y, b.length = M ∧ u ++ b ++ v ∈ language Y)
  (x : Y.carrier) (s : ℕ → ℕ)

theorem BalanceSpecification.MarkerExtension.code_pressure_le_of_exponential_word_bound
    (hs : ∀ n : ℕ, 1 ≤ n → n + M ≤ s n) {ρ : ℝ} (hρ : 0 < ρ)
    {C growthBase B : ℝ}
    (hupper : ∀ n : ℕ, (wordCount (language Y) n : ℝ) ≤ C * growthBase ^ n)
    (hbudget : ∀ L : ℕ, (∑ n ∈ Finset.range L,
      if 1 ≤ n then C * growthBase ^ n / ρ ^ (s n + 1) else 0) ≤ B) (N : ℕ) :
    (∑ l ∈ Finset.range (N + 1),
      (wordCount (code M hM x s) (l + 1) : ℝ) / ρ ^ (l + 1)) ≤ B := by sorry
