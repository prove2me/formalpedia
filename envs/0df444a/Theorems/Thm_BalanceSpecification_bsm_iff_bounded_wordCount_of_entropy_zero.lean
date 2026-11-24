-- Prove2me | Theorems.Thm_BalanceSpecification_bsm_iff_bounded_wordCount_of_entropy_zero
-- name    : BalanceSpecification.bsm_iff_bounded_wordCount_of_entropy_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:53:37.871938+00:00
-- url     : https://prove2.me/theorems/ce4d3774-6e22-4f52-ace8-5bab6bedf2c2
-- title:
--   Balance Specification: bsm iff bounded word Count of entropy zero
-- statement:
--   The counting step in the zero-entropy BSM characterization. Periodicity is a
--   separate dynamical conclusion, not a premise or claim of this lemma.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Entropy.lean#L69-L74
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Entropy.lean#L69-L74

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

theorem BalanceSpecification.bsm_iff_bounded_wordCount_of_entropy_zero {X : ShiftSpace A}
    (hX : X.carrier.Nonempty) (hh : entropy X hX = 0) :
    BoundedlySupermultiplicative (language X) ↔
      BddAbove (Set.range fun n => (wordCount (language X) n : ℝ)) := by sorry
