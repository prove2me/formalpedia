-- Prove2me | Theorems.Thm_BalanceSpecification_MarkerExtension_payloadSuffix_common_tail
-- name    : BalanceSpecification.MarkerExtension.payloadSuffix_common_tail
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:03:02.927413+00:00
-- url     : https://prove2.me/theorems/aae3f81b-24a0-4f26-b35e-51297ee55d81
-- title:
--   Marker Extension: payload Suffix common tail
-- statement:
--   At the minimal eligible index, every payload suffix has the same last
--   `min l b_m` symbols, exactly the common-tail argument in the manuscript.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerSuffix.lean#L105-L118
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerSuffix.lean#L105-L118

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

theorem BalanceSpecification.MarkerExtension.payloadSuffix_common_tail
    (hs : ∀ n : ℕ, 1 ≤ n → n + M ≤ s n)
    (hb : Monotone (suffixLength M s)) {l m : ℕ}
    (hmin : ∀ n : ℕ, 1 ≤ n → l ≤ s n → m ≤ n)
    {z : Word A} (hz : z ∈ payloadSuffixFinset M hM x s l) :
    sourceTail x (min l (suffixLength M s m)) <:+ z := by sorry
