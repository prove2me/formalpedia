-- Prove2me | Theorems.Thm_BalanceSpecification_wordCount_one_le
-- name    : BalanceSpecification.wordCount_one_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:32:28.266512+00:00
-- url     : https://prove2.me/theorems/57e794f5-4dd2-451f-9746-43321d768097
-- title:
--   Balance Specification: word Count one le
-- statement:
--   The Balance Specification construction uses the word Count one le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Entropy.lean#L27-L29
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Entropy.lean#L27-L29

module
public import Definitions.Def_BalanceSpecificaton_CountBounds
public import Definitions.Def_BalanceSpecificaton_Growth
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Entropy
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Filter
open scoped Topology
open BalanceSpecification
variable {A : Type*} [Fintype A] [TopologicalSpace A]

theorem BalanceSpecification.wordCount_one_le {X : ShiftSpace A} (hX : X.carrier.Nonempty) (n : ℕ) :
    (1 : ℝ) ≤ wordCount (language X) n := by sorry
