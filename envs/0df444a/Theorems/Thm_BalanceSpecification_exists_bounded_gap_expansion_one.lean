-- Prove2me | Theorems.Thm_BalanceSpecification_exists_bounded_gap_expansion_one
-- name    : BalanceSpecification.exists_bounded_gap_expansion_one
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:04:38.531911+00:00
-- url     : https://prove2.me/theorems/814be92f-967b-4917-87cc-cb0dead56a38
-- title:
--   Balance Specification: exists bounded gap expansion one
-- statement:
--   Every base strictly between one and two admits a binary expansion of one
--   with bounded successive occupied positions and an occupied position zero.
--   The latter supplies a return word of length one in its S-gap construction.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/EntropyRealization.lean#L170-L224
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/EntropyRealization.lean#L170-L224

module
public import Definitions.Def_BalanceSpecificaton_SGapBounds
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_EntropyRealization
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Filter Set
open scoped Topology
open BalanceSpecification

theorem BalanceSpecification.exists_bounded_gap_expansion_one {β : ℝ} (hβ1 : 1 < β) (hβ2 : β < 2) :
    ∃ S : Set ℕ, 0 ∈ S ∧ HasBoundedSuccessiveGaps S ∧
      (∑' s : S, (β ^ (s.val + 1))⁻¹) = 1 := by sorry
