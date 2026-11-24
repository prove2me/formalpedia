-- Prove2me | Theorems.Thm_BalanceSpecification_MarkerExtension_payloadSuffix_card_exp_bound
-- name    : BalanceSpecification.MarkerExtension.payloadSuffix_card_exp_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:03:09.705737+00:00
-- url     : https://prove2.me/theorems/50144932-6189-467a-964c-cda3ece55e95
-- title:
--   Marker Extension: payload Suffix card exp bound
-- statement:
--   The common-tail count gives the subexponential-in-the-source-base suffix
--   budget needed by the marker construction. Every sequence and source-growth
--   input is displayed; these are construction data, not additional source-root premises.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerSuffix.lean#L156-L184
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerSuffix.lean#L156-L184

module
public import Definitions.Def_BalanceSpecificaton_MarkerExtension
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_MarkerSuffix
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.MarkerExtension
variable {A : Type*} [TopologicalSpace A] {Y : ShiftSpace A}
variable (M : ℕ)
  (hM : ∀ u ∈ language Y, ∀ v ∈ language Y,
    ∃ b ∈ language Y, b.length = M ∧ u ++ b ++ v ∈ language Y)
  (x : Y.carrier) (s : ℕ → ℕ)
variable [Fintype A]

theorem BalanceSpecification.MarkerExtension.payloadSuffix_card_exp_bound {hY : Y.carrier.Nonempty} {C : ℝ}
    (hC : 0 ≤ C)
    (hupper : ∀ n : ℕ, (wordCount (language Y) n : ℝ) ≤
      C * Real.exp ((n : ℝ) * entropy Y hY))
    (hstrict : StrictMono s)
    (hsize : ∀ n : ℕ, 1 ≤ n → 4 * (n + M) ≤ s n)
    (hcofinal : ∀ L : ℕ, ∃ n : ℕ, 1 ≤ n ∧ L ≤ s n) (l : ℕ) :
    ((payloadSuffixFinset M hM x s l).card : ℝ) ≤
      C * Real.exp ((l : ℝ) * entropy Y hY / 4) := by sorry
