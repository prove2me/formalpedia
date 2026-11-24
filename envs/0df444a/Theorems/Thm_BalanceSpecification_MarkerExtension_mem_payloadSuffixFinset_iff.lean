-- Prove2me | Theorems.Thm_BalanceSpecification_MarkerExtension_mem_payloadSuffixFinset_iff
-- name    : BalanceSpecification.MarkerExtension.mem_payloadSuffixFinset_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:02:44.515375+00:00
-- url     : https://prove2.me/theorems/9c231157-3b78-4d8e-92db-2b5a76d1aa48
-- title:
--   Marker Extension: mem payload Suffix Finset iff
-- statement:
--   No language restriction is lost: every payload suffix is admissible.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerSuffix.lean#L92-L101
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerSuffix.lean#L92-L101

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

theorem BalanceSpecification.MarkerExtension.mem_payloadSuffixFinset_iff {l : ℕ} {z : Word A} :
    z ∈ payloadSuffixFinset M hM x s l ↔
      z.length = l ∧ ∃ u : PositiveLanguage Y, z <:+ sourcePayload M hM x s u := by sorry
