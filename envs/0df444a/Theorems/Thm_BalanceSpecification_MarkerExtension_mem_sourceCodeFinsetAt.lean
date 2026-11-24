-- Prove2me | Theorems.Thm_BalanceSpecification_MarkerExtension_mem_sourceCodeFinsetAt
-- name    : BalanceSpecification.MarkerExtension.mem_sourceCodeFinsetAt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:00:02.236521+00:00
-- url     : https://prove2.me/theorems/4d2e9a49-9c38-453c-a94c-4213f9ecfffb
-- title:
--   Marker Extension: mem source Code Finset At
-- statement:
--   The Marker Extension construction uses the mem source Code Finset At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerCodeCounts.lean#L35-L51
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerCodeCounts.lean#L35-L51

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

theorem BalanceSpecification.MarkerExtension.mem_sourceCodeFinsetAt {n : ℕ} {z : Word (Option A)} :
    z ∈ sourceCodeFinsetAt M hM x s n ↔
      ∃ u : PositiveLanguage Y, u.val.length = n ∧
        none :: (sourcePayload M hM x s u).map some = z := by sorry
