-- Prove2me | Theorems.Thm_BalanceSpecification_avoidance_ratio_tendsto_zero_of_vanishing
-- name    : BalanceSpecification.avoidance_ratio_tendsto_zero_of_vanishing
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:08:54.719804+00:00
-- url     : https://prove2.me/theorems/868801c5-2e11-4cfd-b3fd-dddbe3d5e9ee
-- title:
--   Balance Specification: avoidance ratio tendsto zero of vanishing
-- statement:
--   Vanishing avoidance counts are handled directly without taking a logarithm
--   of zero or assigning a false finite entropy to the empty language.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Occurrence.lean#L116-L123
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Occurrence.lean#L116-L123

module
public import Definitions.Def_BalanceSpecificaton_Counting
public import Definitions.Def_BalanceSpecificaton_Growth
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Occurrence
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
open Filter
open scoped Topology
variable {A : Type*} [Fintype A] {L : Set (Word A)}

theorem BalanceSpecification.avoidance_ratio_tendsto_zero_of_vanishing (hL : IsFactorial L)
    (v : Word A) {m : ℕ} (hm : wordCount (avoidingLanguage L v) m = 0) :
    Tendsto
      (fun n : ℕ => (wordCount (avoidingLanguage L v) n : ℝ) / wordCount L n)
      atTop (𝓝 0) := by sorry
