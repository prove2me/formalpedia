-- Prove2me | Theorems.Thm_BalanceSpecification_MarkerExtension_payloadSuffix_card_le_wordCount
-- name    : BalanceSpecification.MarkerExtension.payloadSuffix_card_le_wordCount
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:02:56.464655+00:00
-- url     : https://prove2.me/theorems/ac470726-6e3f-4909-9677-428591f0b845
-- title:
--   Marker Extension: payload Suffix card le word Count
-- statement:
--   Removing the common suffix injects all eligible suffixes into the source
--   words of the remaining length.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerSuffix.lean#L122-L151
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerSuffix.lean#L122-L151

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

theorem BalanceSpecification.MarkerExtension.payloadSuffix_card_le_wordCount
    (hs : ∀ n : ℕ, 1 ≤ n → n + M ≤ s n)
    (hb : Monotone (suffixLength M s)) {l m : ℕ}
    (hmin : ∀ n : ℕ, 1 ≤ n → l ≤ s n → m ≤ n) :
    (payloadSuffixFinset M hM x s l).card ≤
      wordCount (language Y) (l - min l (suffixLength M s m)) := by sorry
