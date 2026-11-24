-- Prove2me | Theorems.Thm_BalanceSpecification_MarkerExtension_code_pressure_le_source_budget
-- name    : BalanceSpecification.MarkerExtension.code_pressure_le_source_budget
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:03:38.325805+00:00
-- url     : https://prove2.me/theorems/515a6c6c-65db-4e0c-9f60-ddf28029d361
-- title:
--   Marker Extension: code pressure le source budget
-- statement:
--   Actual finite generator pressure is bounded by the source-word budget.
--   This counts the literal source code, not a separately assumed coefficient sequence.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerCodeCounts.lean#L113-L175
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerCodeCounts.lean#L113-L175

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

theorem BalanceSpecification.MarkerExtension.code_pressure_le_source_budget
    (hs : ∀ n : ℕ, 1 ≤ n → n + M ≤ s n) {ρ : ℝ} (hρ : 0 < ρ) (N : ℕ) :
    (∑ l ∈ Finset.range (N + 1),
      (wordCount (code M hM x s) (l + 1) : ℝ) / ρ ^ (l + 1)) ≤
      ∑ n ∈ Finset.range (N + 1),
        if 1 ≤ n then (wordCount (language Y) n : ℝ) / ρ ^ (s n + 1) else 0 := by sorry
