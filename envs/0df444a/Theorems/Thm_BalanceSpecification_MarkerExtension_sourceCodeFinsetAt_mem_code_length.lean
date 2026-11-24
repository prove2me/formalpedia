-- Prove2me | Theorems.Thm_BalanceSpecification_MarkerExtension_sourceCodeFinsetAt_mem_code_length
-- name    : BalanceSpecification.MarkerExtension.sourceCodeFinsetAt_mem_code_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:03:30.883902+00:00
-- url     : https://prove2.me/theorems/be24a04b-8f95-4c23-bf27-524af0ed1fb8
-- title:
--   Marker Extension: source Code Finset At mem code length
-- statement:
--   A source generator has length `s_n+1`, and its input index is positive.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerCodeCounts.lean#L70-L78
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerCodeCounts.lean#L70-L78

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

theorem BalanceSpecification.MarkerExtension.sourceCodeFinsetAt_mem_code_length
    (hs : ∀ n : ℕ, 1 ≤ n → n + M ≤ s n)
    {n : ℕ} {z : Word (Option A)} (hz : z ∈ sourceCodeFinsetAt M hM x s n) :
    1 ≤ n ∧ z ∈ code M hM x s ∧ z.length = s n + 1 := by sorry
