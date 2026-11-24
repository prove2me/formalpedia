-- Prove2me | Theorems.Thm_BalanceSpecification_bsm_iff_entropy_ratio
-- name    : BalanceSpecification.bsm_iff_entropy_ratio
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:16:38.087693+00:00
-- url     : https://prove2.me/theorems/828626e3-e8a1-4b4d-ae3c-b814d292e427
-- title:
--   Balance Specification: bsm iff entropy ratio
-- statement:
--   Proposition `prop::BSM_entropy_condition`, on the source's nonempty shifts.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Entropy.lean#L53-L58
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Entropy.lean#L53-L58

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

theorem BalanceSpecification.bsm_iff_entropy_ratio {X : ShiftSpace A} (hX : X.carrier.Nonempty) :
    BoundedlySupermultiplicative (language X) ↔
      ∃ c : ℝ, 1 ≤ c ∧ ∀ n : ℕ,
        1 / c ≤ Real.exp ((n : ℝ) * entropy X hX) / wordCount (language X) n ∧
          Real.exp ((n : ℝ) * entropy X hX) / wordCount (language X) n ≤ 1 := by sorry
