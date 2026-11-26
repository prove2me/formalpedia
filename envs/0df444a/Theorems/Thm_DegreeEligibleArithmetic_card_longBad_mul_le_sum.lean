-- Prove2me | Theorems.Thm_DegreeEligibleArithmetic_card_longBad_mul_le_sum
-- name    : DegreeEligibleArithmetic.card_longBad_mul_le_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:03:51.663839+00:00
-- url     : https://prove2.me/theorems/e33355be-0d11-5c26-a787-5e12e0c68eb7
-- title:
--   Degree Eligible Arithmetic: card long Bad mul le sum
-- statement:
--   The Degree Eligible Arithmetic construction uses the card long Bad mul le sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L1515-L1527
-- source:
--   https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L1515-L1527

module
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Data.Int.Star
public import Mathlib.Combinatorics.Graph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.FinCases
public import Definitions.Def_BirthdayNonbacktracking_Solution
set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSectionVars false
noncomputable section
variable {V : Type*} [Fintype V]
variable (d : ℕ) [NeZero d]
variable (G : SimpleGraph V) (hG : IsRegularOfDegree G d)
attribute [local instance] graphAdjDecidable
attribute [local instance] vertexDecidableEq
open DegreeEligibleArithmetic
variable {ι : Type*} [DecidableEq ι]

theorem DegreeEligibleArithmetic.card_longBad_mul_le_sum (I : Finset ι) (c : ι → ℕ) (L : ℕ) :
    (longBad I c L).card * (L + 1) ≤ ∑ i ∈ I, c i := by sorry
