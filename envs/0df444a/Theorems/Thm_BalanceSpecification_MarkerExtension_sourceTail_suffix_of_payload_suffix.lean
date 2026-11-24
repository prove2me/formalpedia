-- Prove2me | Theorems.Thm_BalanceSpecification_MarkerExtension_sourceTail_suffix_of_payload_suffix
-- name    : BalanceSpecification.MarkerExtension.sourceTail_suffix_of_payload_suffix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:02:42.333047+00:00
-- url     : https://prove2.me/theorems/4d0b8a42-db46-440c-90a2-2cae322c058d
-- title:
--   Marker Extension: source Tail suffix of payload suffix
-- statement:
--   A suffix long enough to contain a chosen common tail necessarily ends in it.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerSuffix.lean#L67-L73
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerSuffix.lean#L67-L73

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

theorem BalanceSpecification.MarkerExtension.sourceTail_suffix_of_payload_suffix {u : PositiveLanguage Y} {z : Word A}
    (hz : z <:+ sourcePayload M hM x s u) {t : ℕ}
    (ht : t ≤ suffixLength M s u.val.length) (htz : t ≤ z.length) :
    sourceTail x t <:+ z := by sorry
