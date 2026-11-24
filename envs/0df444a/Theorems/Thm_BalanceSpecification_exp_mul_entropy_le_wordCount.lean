-- Prove2me | Theorems.Thm_BalanceSpecification_exp_mul_entropy_le_wordCount
-- name    : BalanceSpecification.exp_mul_entropy_le_wordCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:32:48.904418+00:00
-- url     : https://prove2.me/theorems/a17e4ddd-ecfd-4d38-b6e0-2aa3b04cb8aa
-- title:
--   Balance Specification: exp mul entropy le word Count
-- statement:
--   Every finite word count bounds its entropy exponential from below.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Entropy.lean#L48-L50
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Entropy.lean#L48-L50

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

theorem BalanceSpecification.exp_mul_entropy_le_wordCount {X : ShiftSpace A} (hX : X.carrier.Nonempty) (n : ℕ) :
    Real.exp ((n : ℝ) * entropy X hX) ≤ wordCount (language X) n := by sorry
