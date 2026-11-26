-- Prove2me | Theorems.Thm_DegreeEligibleArithmetic_four_mul_card_eligible_ge
-- name    : DegreeEligibleArithmetic.four_mul_card_eligible_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:03:55.530437+00:00
-- url     : https://prove2.me/theorems/fc807801-5607-5e60-9d31-474be3ca3f31
-- title:
--   Degree Eligible Arithmetic: four mul card eligible ge
-- statement:
--   A degree-uniform arithmetic core.  The hypotheses isolate the three
--   simple estimates used later: Markov for long excursions, a degree-`d` bound
--   for each endpoint strip, and the `4d` exceptional endpoints.
--
--   Source: https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L1532-L1611
-- source:
--   https://github.com/benjamin-dozier/birthday-nonbacktracking/blob/7f4be1aae157cadcbb9511bd6b9ee187d60fb662/Solution.lean#L1532-L1611

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

theorem DegreeEligibleArithmetic.four_mul_card_eligible_ge
    (n k d L : ℕ) (I X : Finset ι) (c r j : ι → ℕ)
    (hk : 2 ≤ k)
    (hcardI : k - 1 ≤ I.card)
    (hsum : ∑ i ∈ I, c i ≤ d * n)
    (hX : X.card ≤ 4 * d)
    (hstart : (boundaryBad I r k L).card ≤ L * d)
    (hfinish : (boundaryBad (I \ X) j k L).card ≤ L * d)
    (hlongScale : 16 * (d * n) ≤ k * (L + 1))
    (hboundaryScale : 16 * (L * d) ≤ k)
    (hexceptionScale : 64 * d ≤ k) :
    k ≤ 4 * (eligible I X c r j k L).card := by sorry
